mod common;
use common::*;
use std::path::Path;

fn grpc_dep() -> String {
    format!("[package]\nname = \"p\"\n\n[dependencies]\ngrpc = {{ path = \"{}\" }}\n", repo_root().join("stdlib/grpc").display())
}

const GRPC_SPECS: &str = "use grpc\nbind API as grpc.service.\nThe API shall use gRPC communication.\nThe API GET /foo shall return foo.\n";

fn codes_of(f: &Fixture) -> Vec<String> {
    report_codes(&f.trion(&["verify", "--json"]).json())
}

#[test]
fn reads_the_files_the_entry_includes() {
    let entry = "package p edition \"1\"\ninclude \"spec/a.trion\"\ninclude \"spec/b.trion\"\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("trion.trion", entry), ("spec/a.trion", "The API shall stop.\n"), ("spec/b.trion", "The API shall not stop.\n"), ("other/c.trion", "The API shall run.\n")]);
    let r = f.trion(&["verify"]);
    assert_eq!(r.code, 1, "{}", r.stdout);
    assert!(r.stdout.contains("checked 2 specifications"), "{}", r.stdout);
}

#[test]
fn an_include_is_relative_to_the_including_file() {
    let entry = "package p edition \"1\"\ninclude \"spec/a.trion\"\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("trion.trion", entry), ("spec/a.trion", "include \"deeper/b.trion\"\nnamespace p:\n    The API shall stop.\n"), ("spec/deeper/b.trion", "The API shall not stop.\n")]);
    assert_eq!(codes_of(&f), ["contradiction"]);
}

#[test]
fn the_entry_file_can_be_named_in_the_manifest() {
    let manifest = "[package]\nname = \"p\"\nentry = \"spec/main.trion\"\n";
    let f = Fixture::new(&[("trion.toml", manifest), ("spec/main.trion", "package p edition \"1\"\ninclude \"a.trion\"\n"), ("spec/a.trion", "primitive API\nThe API shall stop.\n")]);
    let r = f.trion(&["verify"]);
    assert_eq!(r.code, 0, "{}", r.stdout);
    assert!(r.stdout.contains("checked 1 specifications"), "{}", r.stdout);
}

#[test]
fn a_file_is_loaded_once_however_often_it_is_included() {
    let entry = "package p edition \"1\"\ninclude \"a.trion\"\ninclude \"./a.trion\"\ninclude \"b.trion\"\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("trion.trion", entry), ("a.trion", "[A] The API shall stop.\n"), ("b.trion", "include \"a.trion\"\nnamespace p:\n")]);
    assert!(codes_of(&f).is_empty(), "a twice-loaded file would duplicate [A]");
}

#[test]
fn an_include_cycle_is_an_error() {
    let entry = "package p edition \"1\"\ninclude \"a.trion\"\n";
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("trion.trion", entry), ("a.trion", "include \"b.trion\"\nnamespace p:\n"), ("b.trion", "include \"a.trion\"\nnamespace p:\n")]);
    assert_eq!(codes_of(&f), ["INCLUDE_CYCLE"]);
}

#[test]
fn a_missing_include_is_an_error() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("trion.trion", "package p edition \"1\"\ninclude \"gone.trion\"\n")]);
    assert_eq!(codes_of(&f), ["MISSING_SOURCE"]);
}

#[test]
fn a_missing_entry_file_is_an_error() {
    let f = Fixture::raw(&[("trion.toml", MANIFEST)]);
    assert_eq!(codes_of(&f), ["MISSING_SOURCE"]);
}

#[test]
fn the_entry_file_declares_the_package_of_the_manifest() {
    let f = Fixture::raw(&[("trion.toml", MANIFEST), ("trion.trion", "namespace p:\n")]);
    assert_eq!(codes_of(&f), ["package-missing"]);
    let f = Fixture::raw(&[("trion.toml", MANIFEST), ("trion.trion", "package q edition \"1\"\n")]);
    assert_eq!(codes_of(&f), ["package-mismatch"]);
}

#[test]
fn an_included_file_has_no_package_declaration() {
    let entry = "package p edition \"1\"\ninclude \"a.trion\"\n";
    let f = Fixture::raw(&[("trion.toml", MANIFEST), ("trion.trion", entry), ("a.trion", "package p edition \"1\"\nnamespace p:\n")]);
    assert_eq!(codes_of(&f), ["package-in-include"]);
}

#[test]
fn a_namespace_begins_with_the_package_name() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "namespace other.api:\n    The API shall stop.\n")]);
    assert_eq!(codes_of(&f), ["namespace-package"]);
}

#[test]
fn composes_specifications_across_files() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("spec/a.trion", "kind is A and B.\n"), ("spec/b.trion", "kind is C.\n")]);
    let r = f.trion(&["verify", "--json"]);
    assert_eq!(report_codes(&r.json()), ["contradiction"]);
    assert_eq!(r.code, 1);
}

#[test]
fn checks_a_single_file_without_a_project() {
    let f = Fixture::new(&[("a.trion", "primitive API\nThe API shall stop.\n")]);
    let r = f.trion(&["verify", "a.trion"]);
    assert_eq!(r.code, 0, "{}", r.stdout);
}

#[test]
fn finds_the_project_from_a_subdirectory() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("spec/a.trion", "primitive API\nThe API shall stop.\n")]);
    let r = trion_in(&f.path().join("spec"), &["verify", "."]);
    assert_eq!(r.code, 0, "{}{}", r.stdout, r.stderr);
    assert!(r.stdout.contains("checked 1 specifications"));
}

#[test]
fn reports_a_missing_project_as_a_usage_error() {
    let f = Fixture::new(&[]);
    let r = f.trion(&["verify"]);
    assert_eq!(r.code, 2);
    assert!(r.stderr.contains("trion.toml"), "{}", r.stderr);
}

#[test]
fn rejects_an_unknown_manifest_field() {
    let f = Fixture::new(&[("trion.toml", "[package]\nname = \"p\"\nspecs = [\"*.trion\"]\n")]);
    assert_eq!(f.trion(&["verify"]).code, 2, "file lists are gone: the entry file includes its files");
}

#[test]
fn a_used_specification_set_detects_a_foreign_operation() {
    let f = Fixture::new(&[("trion.toml", &grpc_dep()), ("a.trion", GRPC_SPECS)]);
    let r = f.trion(&["verify", "--json"]);
    assert_eq!(report_codes(&r.json()), ["shape-violation"], "{}", r.stdout);
}

#[test]
fn without_a_use_the_same_sentences_are_consistent() {
    let f = Fixture::new(&[("trion.toml", &grpc_dep()), ("a.trion", "primitive API\nprimitive API GET /foo\nprimitive gRPC communication\nprimitive foo\nThe API shall use gRPC communication.\nThe API GET /foo shall return foo.\n")]);
    let r = f.trion(&["verify"]);
    assert_eq!(r.code, 0, "{}", r.stdout);
}

#[test]
fn a_use_absent_from_the_manifest_is_an_error() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("spec/a.trion", "use grpc\nThe API shall stop.\n")]);
    assert_eq!(codes_of(&f), ["unresolved-import"]);
}

#[test]
fn a_dependency_with_a_bad_path_is_a_usage_error() {
    let manifest = "[package]\nname = \"p\"\n\n[dependencies]\nx = { path = \"nowhere\" }\n";
    let f = Fixture::new(&[("trion.toml", manifest), ("a.trion", "use x\n")]);
    assert_eq!(f.trion(&["verify"]).code, 2);
}

#[test]
fn dependencies_resolve_transitively_once() {
    let lower = "[package]\nname = \"lower\"\n";
    let upper = "[package]\nname = \"upper\"\n\n[dependencies]\nlower = { path = \"../lower\" }\n";
    let root = "[package]\nname = \"p\"\n\n[dependencies]\nupper = { path = \"upper\" }\nlower = { path = \"lower\" }\n";
    let f = Fixture::new(&[
        ("trion.toml", root),
        ("a.trion", "use upper\nuse lower\nThe API shall stop.\n"),
        ("upper/trion.toml", upper),
        ("upper/u.trion", "use lower\nThe log shall rotate.\n"),
        ("lower/trion.toml", lower),
        ("lower/l.trion", "term API: entity\nThe API shall not stop.\n"),
    ]);
    let r = f.trion(&["verify", "--json"]);
    assert_eq!(report_codes(&r.json()), ["contradiction"], "{}", r.stdout);
}

#[test]
fn the_vocabulary_mode_comes_from_the_manifest() {
    let manifest = "[package]\nname = \"p\"\n\n[vocabulary]\nmode = \"declared\"\n";
    let f = Fixture::new(&[("trion.toml", manifest), ("a.trion", "term API: entity\nterm stop: action\nThe API shall stop.\nThe log shall rotate.\n")]);
    let r = f.trion(&["verify", "--json"]);
    assert_eq!(report_codes(&r.json()), ["UNRESOLVED_TERM"], "{}", r.stdout);
}

#[test]
fn an_unknown_vocabulary_mode_is_an_error() {
    let manifest = "[package]\nname = \"p\"\n\n[vocabulary]\nmode = \"guess\"\n";
    let f = Fixture::new(&[("trion.toml", manifest), ("a.trion", "The API shall stop.\n")]);
    assert_eq!(codes_of(&f), ["manifest-vocabulary-mode"]);
}

#[test]
fn a_parse_error_fails_the_check_and_names_the_line() {
    let f = Fixture::raw(&[("a.trion", "namespace main:\n    The API shall stop.\n    The API for gRPC.\n")]);
    let r = f.trion(&["verify", "a.trion"]);
    assert_eq!(r.code, 1);
    assert!(r.stdout.contains("a.trion:3"), "{}", r.stdout);
}

#[test]
fn warnings_do_not_fail_the_check() {
    let f = Fixture::new(&[("a.trion", "primitive API\nprimitive api\nThe API shall stop.\nThe api shall start.\n")]);
    let r = f.trion(&["verify", "a.trion"]);
    assert_eq!(r.code, 0);
    assert!(r.stdout.contains("warning[vocabulary-similar]"), "{}", r.stdout);
}

#[test]
fn model_prints_contracts_and_formulas() {
    let f = Fixture::new(&[("a.trion", "[S-1] When the user leaves, status is Closed.\n")]);
    let r = f.inspect(&["model", "a.trion"]);
    assert!(r.stdout.contains("S-1"), "{}", r.stdout);
    assert!(r.stdout.contains("assume:    Event(user leave)"), "{}", r.stdout);
    assert!(r.stdout.contains("guarantee: Val(status, Closed)"), "{}", r.stdout);
}

#[test]
fn model_prints_smt2() {
    let f = Fixture::new(&[("a.trion", "kind is A and B.\nkind is C.\n")]);
    let r = f.inspect(&["model", "a.trion", "--smt2"]);
    assert!(r.stdout.contains("(check-sat)"), "{}", r.stdout);
    assert!(r.stdout.contains("(declare-const |Dom(kind, A)| Bool)"), "{}", r.stdout);
}

#[test]
fn vocab_separates_declared_and_inferred_terms() {
    let f = Fixture::new(&[("a.trion", "term API: entity\nThe API shall return foo.\n")]);
    let r = f.inspect(&["vocab", "a.trion"]);
    assert!(r.stdout.lines().any(|l| l.starts_with("API\tdeclared entity")), "{}", r.stdout);
    assert!(r.stdout.lines().any(|l| l.starts_with("foo\tinferred")), "{}", r.stdout);
}

#[test]
fn relate_lists_isolated_specifications_for_review() {
    let f = Fixture::new(&[("a.trion", "The API shall return foo.\nThe printer shall warm up.\n")]);
    let r = f.inspect(&["relate", "a.trion"]);
    assert_eq!(r.code, 0, "unrelated specifications are not a failure");
    assert!(r.stdout.contains("2 isolated specifications"), "{}", r.stdout);
}

#[test]
fn the_verify_command_can_report_json() {
    let f = Fixture::new(&[("a.trion", "The API shall stop.\n")]);
    let report = f.trion(&["verify", "--json", "a.trion"]).json();
    for part in ["diagnostics", "consistency", "sources", "gates"] {
        assert!(!report[part].is_null(), "{part}");
    }
    assert!(Path::new(env!("CARGO_BIN_EXE_trion")).ends_with("trion"));
}

// Namespaces are declared in the files, never derived from directories.

fn tree_codes(files: &[(&str, &str)]) -> Vec<String> {
    let mut all = vec![("trion.toml", MANIFEST)];
    all.extend_from_slice(files);
    codes_of(&Fixture::new(&all))
}

#[test]
fn specs_can_nest_in_directories() {
    let files = [("trion.toml", MANIFEST), ("top.trion", "primitive API\nThe API shall stop.\n"), ("a/b/c.trion", "primitive bell\nThe bell shall ring.\n")];
    let r = Fixture::new(&files).trion(&["verify", "--json"]);
    assert_eq!(r.code, 0, "{}", r.stdout);
    let printed = Fixture::new(&files).trion(&["verify"]).stdout;
    assert!(printed.lines().any(|line| line.starts_with("checked 2 specifications: 0 errors, ") && line.ends_with("; 0/0 checks proved, 0 examples run")), "{printed}");
}

#[test]
fn a_directory_is_not_a_namespace() {
    assert_eq!(tree_codes(&[("api/a.trion", "The API shall stop.\n"), ("web/b.trion", "The API shall not stop.\n")]), ["contradiction"]);
}

#[test]
fn the_vocabulary_names_the_namespace_of_each_term() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "namespace p.api:\n    The bell shall ring.\n")]);
    assert!(f.inspect(&["vocab", "--json"]).stdout.contains("\"namespace\": \"api\""));
}

#[test]
fn namespaces_are_separate() {
    assert!(tree_codes(&[("a.trion", "namespace p.api:\n    The API shall stop.\n"), ("b.trion", "namespace p.web:\n    The API shall not stop.\n")]).is_empty());
}

#[test]
fn a_namespace_can_be_reopened_in_another_file() {
    assert_eq!(tree_codes(&[("a.trion", "namespace p.api:\n    The API shall stop.\n"), ("x/b.trion", "namespace p.api:\n    The API shall not stop.\n")]), ["contradiction"]);
}

#[test]
fn a_use_reaches_another_namespace() {
    let codes = tree_codes(&[("a.trion", "namespace p.api:\n    term API: entity\n    The API shall stop.\n"), ("b.trion", "namespace p.web:\n    use p.api\n    The API shall not stop.\n")]);
    assert_eq!(codes, ["contradiction"]);
}

#[test]
fn a_use_exposes_only_declared_terms() {
    assert!(tree_codes(&[("a.trion", "namespace p.api:\n    The API shall stop.\n"), ("b.trion", "namespace p.web:\n    use p.api\n    The API shall not stop.\n")]).is_empty());
}

#[test]
fn a_child_namespace_does_not_see_its_parent() {
    assert!(tree_codes(&[("a.trion", "namespace p:\n    term API: entity\n    The API shall stop.\n"), ("b.trion", "namespace p.sub:\n    The API shall not stop.\n")]).is_empty());
}

#[test]
fn an_alias_is_closed_within_its_namespace() {
    let api = "namespace p.api:\n    term API: entity\n    alias the service = API\n    The service shall stop.\n";
    let web = "namespace p.web:\n    The service shall not stop.\n    The API shall not stop.\n";
    assert!(tree_codes(&[("a.trion", api), ("b.trion", web)]).is_empty(), "neither the alias nor its term is a name in p.web");
    let web = "namespace p.web:\n    use p.api\n    The service shall not stop.\n";
    assert_eq!(tree_codes(&[("a.trion", api), ("b.trion", web)]), ["contradiction"], "a use brings the alias as a member of p.api");
}

#[test]
fn a_qualified_name_reaches_a_namespace() {
    assert_eq!(tree_codes(&[("a.trion", "namespace p.api:\n    The API shall stop.\n"), ("b.trion", "namespace p.web:\n    The api::API shall not stop.\n")]), ["contradiction"]);
}

#[test]
fn an_unknown_namespace_is_an_error() {
    assert_eq!(tree_codes(&[("b.trion", "namespace p.web:\n    The nope::API shall stop.\n")]), ["namespace-unknown"]);
}

#[test]
fn a_term_from_two_uses_is_ambiguous() {
    let codes = tree_codes(&[
        ("x.trion", "namespace p.a:\n    term API: entity\n"),
        ("y.trion", "namespace p.b:\n    term API: entity\n"),
        ("z.trion", "namespace p.c:\n    use p.a\n    use p.b\n    The API shall stop.\n"),
    ]);
    assert_eq!(codes, ["AMBIGUOUS_TERM"]);
}

#[test]
fn a_use_names_a_namespace_or_a_dependency() {
    assert_eq!(tree_codes(&[("z.trion", "namespace p.c:\n    use nowhere\n    The API shall stop.\n")]), ["unresolved-import"]);
    assert_eq!(tree_codes(&[("z.trion", "namespace p.c:\n    use p.nowhere\n    The API shall stop.\n")]), ["namespace-unknown"]);
    assert!(tree_codes(&[("x.trion", "namespace p.a:\n    The bell shall ring.\n"), ("z.trion", "namespace p.c:\n    use p.a\n    The API shall stop.\n")]).is_empty());
}

#[test]
fn a_namespace_role_binds_like_a_package_role() {
    let role = "namespace p.shapes:\n    role service:\n        activate: The $subject shall use gRPC communication.\n        form METHOD: The $subject $operation shall $action. where $operation does not match /^[A-Z]+ /\n";
    let spec = "namespace p.svc:\n    use p.shapes\n    The API shall use gRPC communication.\n    The API `GET /foo` shall return foo.\n";
    assert_eq!(tree_codes(&[("g.trion", role), ("s.trion", spec)]), ["shape-violation"]);
}
