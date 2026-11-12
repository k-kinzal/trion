fn main() {
    for s in std::env::args().skip(1) {
        if s.ends_with(".trion") {
            let src = std::fs::read_to_string(&s).unwrap();
            let (parsed, diags) = trion_language::parse_document(&src, &s);
            let specs: usize = parsed.documents.iter().map(|d| d.specs.len()).sum();
            println!("== {s}: {specs} specs, {} diagnostics", diags.len());
            for d in diags {
                println!("{}: {} | {}", d.code, d.message, d.refs.first().map(|r| format!("{}: {}", r.line, r.text)).unwrap_or_default());
            }
            continue;
        }
        match trion_language::parse_sentence(&s) {
            Ok(x) => { println!("OK  {s}\n    {:?}", x.core); if std::env::var("FRAMES").is_ok() { println!("    FRAMES {:?}", x.frames); } }
            Err(e) => println!("ERR {s}\n    {e}"),
        }
    }
}
