use trion_analysis::{Observation, Settings};
use trion_boolean::{solve, BackendSettings, Request};

pub const SETTINGS: Settings = Settings {
    backend: BackendSettings {
        max_assignments: 16,
        timeout_ms: 1_000,
    },
    reference_assignments: 16,
};

pub fn worker(request: &Request) -> Observation {
    Observation::Response(serde_json::to_string(&solve(request).unwrap()).unwrap())
}
