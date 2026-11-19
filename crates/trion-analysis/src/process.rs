//! Isolate worker termination and avoid pipe deadlocks during polling.

use crate::Observation;
use std::io::{self, Read, Seek, SeekFrom};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};
use trion_boolean::Request;

const MAX_OUTPUT_BYTES: u64 = 1_048_576;

fn stop(child: &mut Child) -> io::Result<()> {
    // A concurrent exit can make kill fail. Always reap and report wait errors.
    let _ = child.kill();
    child.wait().map(|_| ())
}

fn execute(
    command: &mut Command,
    request: &Request,
) -> Result<Observation, Box<dyn std::error::Error>> {
    let limit = Duration::from_millis(request.settings.timeout_ms);
    if limit.is_zero() {
        return Ok(Observation::Timeout);
    }
    let mut input = tempfile::tempfile()?;
    serde_json::to_writer(&mut input, request)?;
    input.seek(SeekFrom::Start(0))?;
    let mut output = tempfile::tempfile()?;
    let start = Instant::now();
    let mut child = command
        .stdin(input)
        .stdout(output.try_clone()?)
        .stderr(Stdio::null())
        .spawn()?;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {}
            Err(error) => {
                let _ = stop(&mut child);
                return Err(error.into());
            }
        }
        let remaining = limit.saturating_sub(start.elapsed());
        if remaining.is_zero() {
            stop(&mut child)?;
            return Ok(Observation::Timeout);
        }
        std::thread::sleep(remaining.min(Duration::from_millis(5)));
    };
    if !status.success() {
        return Ok(Observation::BackendFailure(format!(
            "worker exited with {status}"
        )));
    }
    output.seek(SeekFrom::Start(0))?;
    let mut bytes = Vec::new();
    output.take(MAX_OUTPUT_BYTES + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_OUTPUT_BYTES {
        return Ok(Observation::UnusableOutput(
            "worker output exceeded 1 MiB".into(),
        ));
    }
    Ok(match String::from_utf8(bytes) {
        Ok(text) => Observation::Response(text),
        Err(_) => Observation::UnusableOutput("worker output is not UTF-8".into()),
    })
}

pub fn run_worker(command: &mut Command, request: &Request) -> Observation {
    execute(command, request).unwrap_or_else(|error| Observation::BackendFailure(error.to_string()))
}
