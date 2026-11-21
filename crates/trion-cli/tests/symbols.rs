//! Regression tests for name resolution, conservative abbreviations and
//! application of pinned specification sets.

mod common;
use common::*;
use serde_json::Value;

const MANIFEST: &str = "[package]\nname = \"main\"\n";

fn document(body: &str) -> Fixture {
    let text = format!(
        "package main\nnamespace main:\n{}",
        body.lines()
            .map(|line| format!("    {line}\n"))
            .collect::<String>()
    );
    Fixture::raw(&[("trion.toml", MANIFEST), ("trion.trion", &text)])
}

fn verified(fixture: &Fixture) -> Value {
    fixture
        .verify(&["--json", "--scope", "2", "--trace-length", "3"])
        .json()
}

fn contract<'a>(report: &'a Value, id: &str) -> &'a Value {
    report["contracts"]
        .as_array()
        .unwrap()
        .iter()
        .find(|contract| contract["statement"]["id"] == id)
        .unwrap_or_else(|| panic!("{id} in {report}"))
}

#[test]
fn nominal_restriction_constrains_its_subject() {
    use trion_language::syntax::ast::{Core, NpGroup, Predicate, RelativeBody};
    let sentence = trion_language::parse_sentence(
        "The codec is a specification language that is also a controlled language.",
    )
    .unwrap();
    let Core::Description {
        predicate:
            Predicate::Words {
                nominal: Some(NpGroup::Single(category)),
                ..
            },
        ..
    } = sentence.core
    else {
        panic!("missing nominal predicate");
    };
    let restriction = category
        .relative
        .expect("the category keeps its relative clause");
    assert!(matches!(
        restriction.body,
        RelativeBody::Copular {
            predicate: Predicate::Words {
                nominal: Some(NpGroup::Single(_)),
                ..
            },
            ..
        }
    ));
    let start = "system codec, schema\n[EX] There is a codec.\n[EX2] There is a schema.\n";
    let compound =
        "[LANG] The codec is a specification language that is also a controlled language.\n";
    let expanded = "[LANG] The codec is a specification language.\n[CNL] The codec is a controlled language.\n";
    let common = "[OTHER] The schema is a specification language.\n[NEG] The schema is not a controlled language.\n";
    let compound_doc = document(&format!("{start}{compound}{common}"));
    let expanded_doc = document(&format!("{start}{expanded}{common}"));
    let report = compound_doc.convert(&["--json"]).json();
    let flat = expanded_doc.convert(&["--json"]).json();
    assert_eq!(report["conforms"], true, "{report}");
    assert_eq!(contract(&report, "LANG")["role"], "guarantee");
    assert_eq!(
        contract(&report, "LANG")["guarantee"],
        serde_json::json!({ "And": [
        contract(&flat, "LANG")["guarantee"],
        contract(&flat, "CNL")["guarantee"],
    ] })
    );
    assert_eq!(verdicts(&verified(&compound_doc))["consistency"], "proved");
    let contradicted = document(&format!(
        "{start}{compound}{common}[BAD] The codec is not a controlled language.\n"
    ));
    let report = verified(&contradicted);
    assert_eq!(verdicts(&report)["consistency"], "refuted", "{report}");
}

#[test]
fn abbreviations_expand_both_ways_without_adding_assumptions() {
    let base = "system codec\n[EX] There is a codec.\n[BASE] The codec is a specification language.\n[CNL] The codec is a controlled language.\n";
    let definitions = "A precise language means a disciplined language.\nA disciplined language means a specification language that is a controlled language.\n";
    let with = document(&format!("{base}{definitions}"));
    let before = document(base).convert(&["--json"]).json();
    let after = with.convert(&["--json"]).json();
    assert_eq!(before["conforms"], true, "{before}");
    assert_eq!(after["conforms"], true, "{after}");
    assert_eq!(before["contracts"], after["contracts"]);
    let contradicted = document(&format!(
        "{base}{definitions}[BAD] The codec is not a precise language.\n"
    ));
    let report = verified(&contradicted);
    assert_eq!(verdicts(&report)["consistency"], "refuted", "{report}");

    let inclusion = document(&format!("{base}Each precise language is a specification language.\n[BAD] The codec is not a precise language.\n"));
    assert_eq!(verdicts(&verified(&inclusion))["consistency"], "proved");
}

#[test]
fn definitions_cannot_supply_unknown_or_ill_typed_meanings() {
    for (definition, expected) in [
        (
            "A precise language means an unknown classification.",
            "UNRESOLVED_TERM",
        ),
        (
            "A precise language means a language that is able to compile.",
            "UNSUPPORTED_SEMANTICS",
        ),
        (
            "A precise language means a marker.",
            "vocabulary-kind-conflict",
        ),
        (
            "A precise language means a precise language.",
            "CYCLIC_DEFINITION",
        ),
        ("A marker means a language.", "NAME_COLLISION"),
    ] {
        let fixture = document(&format!(
            "system codec\nterm marker: value\nThe codec is a language.\n{definition}"
        ));
        let report = fixture.convert(&["--json"]).json();
        assert_eq!(report["conforms"], false, "{report}");
        assert!(
            report_codes(&report).iter().any(|code| code == expected),
            "{expected}: {report}"
        );
    }
}

#[test]
fn long_definition_chains_are_checked_even_when_unused() {
    use std::fmt::Write;

    let mut definitions = String::new();
    for i in 0..65 {
        writeln!(definitions, "A category{i} means a category{}.", i + 1).unwrap();
    }
    let acyclic = document(&format!(
        "{definitions}A category65 means a base classification.\nterm base classification: class"
    ));
    let report = acyclic.convert(&["--json"]).json();
    assert_eq!(report["conforms"], true, "{report}");

    let cyclic = document(&format!("{definitions}A category65 means a category0."));
    let report = cyclic.convert(&["--json"]).json();
    assert_eq!(report["conforms"], false, "{report}");
    assert!(
        report_codes(&report)
            .iter()
            .any(|code| code == "CYCLIC_DEFINITION"),
        "{report}"
    );
}

#[test]
fn imported_description_keeps_its_owner_and_reports_ambiguity() {
    let project = Fixture::raw(&[
        ("trion.toml", MANIFEST),
        (
            "trion.trion",
            r#"
package main
namespace main.catalog:
    The codec is a specification language.
namespace main.app:
    use main.catalog
    alias serializer = codec
    [JOB] The serializer shall store a message.
"#,
        ),
    ]);
    let report = project.convert(&["--json"]).json();
    assert_eq!(report["conforms"], true, "{report}");
    assert!(contract(&report, "JOB")["guarantee"]
        .to_string()
        .contains("catalog::codec|store message"));
    project.write(
        "trion.trion",
        r#"
package main
namespace main.first:
    The codec is a specification language.
namespace main.second:
    The codec is a specification language.
namespace main.app:
    use main.first
    use main.second
    The codec is a controlled language.
"#,
    );
    let ambiguous = project.convert(&["--json"]).json();
    assert!(
        report_codes(&ambiguous).contains(&"AMBIGUOUS_TERM".to_string()),
        "{ambiguous}"
    );
}

#[test]
fn definition_and_alias_targets_must_have_one_owner() {
    let preamble = r#"
package main
namespace main.first:
    The codec is a specification language.
namespace main.second:
    The codec is a specification language.
namespace main.app:
    use main.first
    use main.second
"#;
    for sentence in [
        "alias serializer = codec",
        "A supported language means a specification language.",
    ] {
        let project = Fixture::raw(&[
            ("trion.toml", MANIFEST),
            ("trion.trion", &format!("{preamble}    {sentence}\n")),
        ]);
        let report = project.convert(&["--json"]).json();
        assert_eq!(report["conforms"], false, "{report}");
        assert!(
            report_codes(&report)
                .iter()
                .any(|code| code == "AMBIGUOUS_TERM"),
            "{report}"
        );
    }
}

#[test]
fn local_names_win_over_imported_aliases_and_compound_names_keep_their_identity() {
    let project = Fixture::raw(&[
        ("trion.toml", MANIFEST),
        (
            "trion.trion",
            r#"
package main
namespace main.catalog:
    The target is a specification language.
    alias codec = target
namespace main.app:
    use main.catalog
    system codec
    alias buffer = codec
    [JOB] The codec shall store a buffer status.
    [OPEN] The buffer shall start.
"#,
        ),
    ]);
    let report = project.convert(&["--json"]).json();
    assert_eq!(report["conforms"], true, "{report}");
    assert!(contract(&report, "JOB")["guarantee"]
        .to_string()
        .contains("app::codec|store buffer status"));
    assert!(contract(&report, "OPEN")["guarantee"]
        .to_string()
        .contains("app::codec|start"));
}

const APPLICATION: &str = r#"
package main
namespace main:
    refer wire
    system sender1, sender2
    [EX1] There is a sender1.
    [EX2] There is a sender2.
    [EX3] There is a receipt.
"#;

fn project(body: &str) -> Fixture {
    Fixture::raw(&[
        (
            "trion.toml",
            "[package]\nname = \"main\"\n[dependencies]\nwire.path = \"wire\"\n",
        ),
        ("trion.trion", &format!("{APPLICATION}{body}")),
        ("wire/trion.toml", "[package]\nname = \"receipt-profile\"\n"),
        (
            "wire/trion.trion",
            r#"
package receipt-profile
namespace receipt-profile:
    system endpoint
    [EMIT] The endpoint shall send a reply.
"#,
        ),
    ])
}

#[test]
fn reference_application_and_readback() {
    let reject = "    [LOCAL] The sender2 shall not send the receipt.\n";
    let positive = "    apply wire as first with endpoint = sender1, reply = receipt\n";
    let negative = "    apply wire as second with endpoint = sender2, reply = receipt\n";
    let ref_only = project(reject);
    let ref_only_report = verified(&ref_only);
    assert_eq!(
        ref_only_report["references"][0]["package"],
        "receipt-profile"
    );
    assert_eq!(ref_only_report["applications"], serde_json::json!([]));
    assert_eq!(verdicts(&ref_only_report)["consistency"], "proved");
    assert!(!ref_only_report
        .to_string()
        .contains("receipt-profile::apply"));
    let one = project(&format!("{positive}{reject}"));
    assert_eq!(verdicts(&verified(&one))["consistency"], "proved");
    let two = project(&format!("{positive}{negative}{reject}    alias receiver = sender1\n    predicate spare(entity, object)\n"));
    let converted = two.convert(&["--json", "--out", "result"]).json();
    assert_eq!(converted["conforms"], true, "{converted}");
    assert_eq!(converted["applications"].as_array().unwrap().len(), 2);
    let form = trioc_cli::mmt::Form::read_path(&two.path().join("result")).unwrap();
    assert_eq!(form.applications.len(), 2);
    assert_eq!(form.references[0].package, "receipt-profile");
    let symbol = |name: &str| {
        form.symbols
            .iter()
            .find(|symbol| symbol.name == name)
            .unwrap()
    };
    let target = symbol("sender1");
    assert_eq!(symbol("receiver").identity, target.identity);
    assert_eq!(symbol("receiver").targets, ["sender1"]);
    assert!(target.constraints.iter().any(|at| at.id == "EX1"));
    assert_eq!(
        symbol("spare").signature.as_deref().unwrap(),
        ["entity", "object"]
    );
    assert_eq!(
        converted["symbols"],
        serde_json::to_value(&form.symbols).unwrap()
    );
    let report = verified(&two);
    assert_eq!(verdicts(&report)["consistency"], "refuted", "{report}");
    assert!(report.to_string().contains("apply-second/EMIT"), "{report}");
    let missing = project("    apply wire as first with reply = receipt\n")
        .convert(&["--json"])
        .json();
    assert_eq!(missing["conforms"], false, "{missing}");
    assert!(missing.to_string().contains("missing mapping for"));
}

#[test]
fn application_resolves_the_mapping_and_can_supply_the_existence_contract() {
    let fixture = project("    apply wire as first with endpoint = sender1, reply = payload\n");
    let base = fixture.read("trion.trion").replace(
        "    [EX1] There is a sender1.\n",
        "    use main.left\n    use main.right\n",
    );
    let text = format!(
        "{base}\nnamespace main.left:\n    There is a payload.\nnamespace main.right:\n    There is a payload.\n"
    );
    fixture.write(
        "wire/trion.trion",
        &format!(
            "{}    [EXISTS] There is an endpoint.\n",
            fixture.read("wire/trion.trion")
        ),
    );
    fixture.write("trion.trion", &text);
    let report = fixture.convert(&["--json"]).json();
    assert_eq!(report["conforms"], false, "{report}");
    assert!(
        report
            .to_string()
            .contains("`payload` is ambiguous between left and right"),
        "{report}"
    );

    fixture.write(
        "trion.trion",
        &text.replace("reply = payload", "reply = left::payload"),
    );
    let report = verified(&fixture);
    let exists = contract(&report, "receipt-profile::apply-first/EXISTS");
    assert_eq!(exists["role"], "guarantee");
    assert!(exists["guarantee"].to_string().contains("sender1"));
    let emit = contract(&report, "receipt-profile::apply-first/EMIT");
    assert!(emit["guarantee"]
        .to_string()
        .contains("sender1|send left::payload"));
}

#[test]
fn specification_application_maps_explicit_individual_types() {
    let fixture = project("    apply wire as north with endpoint = sender1, reply = receipt\n    apply wire as south with endpoint = sender2, reply = receipt\n");
    fixture.write(
        "trion.trion",
        &fixture.read("trion.trion").replace(
            "    system sender1, sender2",
            "    individuals sender1, sender2\n    system sender1, sender2",
        ),
    );
    fixture.write(
        "wire/trion.trion",
        &fixture
            .read("wire/trion.trion")
            .replace(
                "    system endpoint",
                "    individuals endpoint\n    system endpoint",
            )
            .replace("The endpoint shall", "Each endpoint shall"),
    );
    let before = verified(&fixture);
    assert_eq!(before["conforms"], true, "{before}");
    assert_eq!(verdicts(&before)["consistency"], "proved", "{before}");
    fixture.write(
        "trion.trion",
        &format!(
            "{}    [VIOLATION] Each sender2 shall not send the receipt.\n",
            fixture.read("trion.trion"),
        ),
    );
    let after = verified(&fixture);
    assert_eq!(verdicts(&after)["consistency"], "refuted", "{after}");
    assert!(after.to_string().contains("apply-south/EMIT"), "{after}");

    fixture.write(
        "trion.trion",
        &fixture
            .read("trion.trion")
            .replace("    individuals sender1, sender2\n", ""),
    );
    let wrong_domain = fixture.convert(&["--json"]).json();
    assert_eq!(wrong_domain["conforms"], false, "{wrong_domain}");
    assert!(
        wrong_domain
            .to_string()
            .contains("expects a declared type of individuals"),
        "{wrong_domain}"
    );
}

#[test]
fn applied_inclusion_is_rederived_with_the_mapped_carrier_and_requested_bound() {
    let root = "package main\nnamespace main:\n    refer wire\n    individuals sender, client\n    system sender, client\n    [EX] There is a sender.\n    apply wire as profile with endpoint = sender, terminal = client\n";
    let fixture = Fixture::raw(&[
        ("trion.toml", "[package]\nname = \"main\"\n[dependencies]\nwire.path = \"wire\"\n"),
        ("trion.trion", root),
        ("wire/trion.toml", "[package]\nname = \"wire\"\n"),
        ("wire/trion.trion", "package wire\nnamespace wire:\n    individuals endpoint, terminal\n    system endpoint, terminal\n    [CLASS] Each endpoint is a terminal.\n"),
    ]);
    let verify = || {
        fixture
            .verify(&["--json", "--properties", "--scope", "2"])
            .json()
    };
    let positive = verify();
    assert_eq!(positive["conforms"], true, "{positive}");
    assert_eq!(verdicts(&positive)["consistency"], "proved");
    assert_eq!(positive["checked"]["derivations"]["texts"], 1);

    fixture.write(
        "trion.trion",
        &format!("{root}    [NO] No sender is a client.\n"),
    );
    let negative = verify();
    assert_eq!(negative["conforms"], true, "{negative}");
    assert_eq!(verdicts(&negative)["consistency"], "refuted", "{negative}");
    assert!(negative.to_string().contains("apply-profile/CLASS"));

    let mixed = document(
        "individuals sender, client\nsystem sender\nenvironment client\nEach sender is a client.\n",
    )
    .convert(&["--json"])
    .json();
    assert_eq!(mixed["conforms"], false, "{mixed}");
    assert!(
        mixed
            .to_string()
            .contains("both system and environment responsibility"),
        "{mixed}"
    );
}

#[test]
fn applying_a_specification_includes_its_use_dependencies_once() {
    let fixture = project("");
    fixture.write(
        "wire/trion.toml",
        "[package]\nname = \"receipt-profile\"\n[dependencies]\nstore.path = \"store\"\n",
    );
    fixture.write(
        "wire/trion.trion",
        &fixture
            .read("wire/trion.trion")
            .replace("    system endpoint", "    use store\n    system endpoint"),
    );
    fixture.write("wire/store/trion.toml", "[package]\nname = \"store\"\n");
    fixture.write(
        "wire/store/trion.trion",
        r#"package store
namespace store:
    system logger
    [SAVE] The logger shall store a record.
"#,
    );
    let input = fixture.read("trion.trion");
    fixture.write(
        "trion.trion",
        &format!("{input}    [NO] The sender2 shall not store the receipt.\n"),
    );
    let reference = verified(&fixture);
    assert_eq!(verdicts(&reference)["consistency"], "proved", "{reference}");

    fixture.write("trion.trion", &format!(
        "{}    apply wire as two with endpoint = sender1, reply = receipt, store::logger = sender2, store::record = receipt\n",
        fixture.read("trion.trion"),
    ));
    let report = verified(&fixture);
    assert_eq!(report["conforms"], true, "{report}");
    assert_eq!(verdicts(&report)["consistency"], "refuted", "{report}");
    assert_eq!(
        report["applications"][0]["dependencies"],
        serde_json::json!(["store"])
    );
    assert!(
        report.to_string().contains("store::apply-two/SAVE"),
        "{report}"
    );
}

#[test]
fn an_applied_predicate_requires_a_compatible_argument_mapping() {
    let fixture = project(
        "    predicate dispatch(sender1, receipt)\n    apply wire as first with endpoint = sender1, reply = receipt, send = dispatch\n",
    );
    fixture.write(
        "wire/trion.trion",
        &fixture.read("wire/trion.trion").replace(
            "    [EMIT]",
            "    term reply: object\n    predicate send(endpoint, reply)\n    [EMIT]",
        ),
    );
    let positive = verified(&fixture);
    assert_eq!(positive["conforms"], true, "{positive}");
    assert_eq!(verdicts(&positive)["consistency"], "proved", "{positive}");
    assert!(
        contract(&positive, "receipt-profile::apply-first/EMIT")["guarantee"]
            .to_string()
            .contains("sender1|dispatch receipt")
    );
    let input = fixture.read("trion.trion");
    fixture.write(
        "trion.trion",
        &input.replace("dispatch(sender1, receipt)", "dispatch(sender2, receipt)"),
    );
    let wrong = fixture.convert(&["--json"]).json();
    assert_eq!(wrong["conforms"], false, "{wrong}");
    assert!(
        wrong
            .to_string()
            .contains("expects signature (sender1, receipt)"),
        "{wrong}"
    );
    fixture.write(
        "trion.trion",
        &format!("{input}    [NO] The sender1 shall not dispatch the receipt.\n"),
    );
    assert_eq!(verdicts(&verified(&fixture))["consistency"], "refuted");
}

#[test]
fn different_namespaces_own_distinct_declared_actions_with_the_same_spelling() {
    let input = r#"package main
namespace main.lib:
    predicate send(entity, object)
namespace main.local:
    predicate send(entity, object)
namespace main.api:
    use main.lib
    use main.local
    system codec
    There is a receipt.
    [LIB] The codec shall lib::send the receipt.
    [LOCAL] The codec shall not local::send the receipt.
"#;
    let fixture = Fixture::raw(&[("trion.toml", MANIFEST), ("trion.trion", input)]);
    let report = verified(&fixture);
    assert_eq!(report["conforms"], true, "{report}");
    assert_eq!(verdicts(&report)["consistency"], "proved", "{report}");
    assert!(contract(&report, "LIB")["guarantee"]
        .to_string()
        .contains("|lib::send"));
    assert!(contract(&report, "LOCAL")["guarantee"]
        .to_string()
        .contains("|local::send"));
    fixture.write(
        "trion.trion",
        &input.replace("not local::send", "not lib::send"),
    );
    assert_eq!(verdicts(&verified(&fixture))["consistency"], "refuted");
}

#[test]
fn an_applied_abbreviation_is_expanded_in_its_origin_and_mapped_at_its_leaves() {
    let fixture = project(
        "    The sender2 is a configured service.\n    The sender2 is an audited service.\n    apply wire as first with endpoint = sender1, reply = receipt, active profile = configured service, signed profile = audited service\n",
    );
    fixture.write(
        "wire/trion.trion",
        &format!(
            "{}    term active profile: class\n    term signed profile: class\n    [PROFILE] A certified profile means an active profile that is a signed profile.\n    [READY] The endpoint is a certified profile.\n",
            fixture.read("wire/trion.trion")
        ),
    );
    let positive = verified(&fixture);
    assert_eq!(positive["conforms"], true, "{positive}");
    assert_eq!(verdicts(&positive)["consistency"], "proved", "{positive}");
    let applied = contract(&positive, "receipt-profile::apply-first/READY");
    let guarantee = applied["guarantee"].to_string();
    assert!(guarantee.contains("class configured service"), "{applied}");
    assert!(guarantee.contains("class audited service"), "{applied}");
    assert!(!guarantee.contains("certified profile"), "{applied}");
    assert!(!positive["applications"][0]["statements"]
        .to_string()
        .contains("PROFILE"));

    fixture.write(
        "trion.trion",
        &format!(
            "{}    [NO] The sender1 is not an audited service.\n",
            fixture.read("trion.trion")
        ),
    );
    let conflict = verified(&fixture);
    assert_eq!(verdicts(&conflict)["consistency"], "refuted", "{conflict}");
    assert!(conflict.to_string().contains("apply-first/READY"));
}

#[test]
fn specification_application_carries_an_explicit_source_form_binding() {
    let fixture = project("    apply wire as first with endpoint = sender1, reply = receipt\n");
    fixture.write(
        "wire/trion.trion",
        &format!(
            "{}    role emitter:\n        required SEND: The $subject shall send a $object.\n    bind endpoint as receipt-profile.emitter.\n",
            fixture.read("wire/trion.trion")
        ),
    );
    let positive = verified(&fixture);
    assert_eq!(positive["conforms"], true, "{positive}");
    assert_eq!(verdicts(&positive)["consistency"], "proved", "{positive}");

    fixture.write(
        "wire/trion.trion",
        &fixture.read("wire/trion.trion").replace(
            "required SEND: The $subject shall send a $object.",
            "required START: The $subject shall start.",
        ),
    );
    let missing = fixture.convert(&["--json"]).json();
    assert_eq!(missing["conforms"], false, "{missing}");
    assert!(
        missing.to_string().contains("missing-required-form"),
        "{missing}"
    );
    assert!(
        missing.to_string().contains("sender1 is bound"),
        "{missing}"
    );
    assert!(missing.to_string().contains("apply-first"), "{missing}");
}

#[test]
fn an_applied_block_narrows_its_assumption_to_its_own_statements() {
    let root = concat!(
        "    environment signal, guard\n",
        "    The signal is a powered feature.\n",
        "    The guard is not an enabled guard.\n",
        "    [DENY-STOP] The sender1 shall not stop.\n",
        "    apply wire as first with endpoint = sender1, reply = receipt, trigger = signal, watcher = guard, feature = powered feature, gatekeeper = enabled guard\n",
    );
    let fixture = project(root);
    fixture.write(
        "wire/trion.trion",
        &format!(
            "{}\n{}",
            fixture.read("wire/trion.trion"),
            r#"    environment trigger, watcher
    While the trigger is a feature:
        [WATCH] The watcher is a gatekeeper.
        [SCOPED] The endpoint shall stop.
"#,
        ),
    );
    let accepted = verified(&fixture);
    assert_eq!(accepted["conforms"], true, "{accepted}");
    assert_eq!(verdicts(&accepted)["consistency"], "proved", "{accepted}");
    let watch = contract(&accepted, "receipt-profile::apply-first/WATCH");
    assert!(watch["scope"]["head"]
        .as_str()
        .unwrap()
        .contains("While the trigger is a feature"));

    fixture.write(
        "trion.trion",
        &format!("{APPLICATION}{root}    [DENY-SEND] The sender1 shall not send the receipt.\n"),
    );
    let rejected = verified(&fixture);
    assert_eq!(verdicts(&rejected)["consistency"], "refuted", "{rejected}");
    assert!(rejected.to_string().contains("apply-first/EMIT"));
}

#[test]
fn application_maps_every_class_in_a_compound_nominal_predicate() {
    let fixture = project(concat!(
        "    [SUMMARY] The sender1 is a monitoring service.\n",
        "    [DENIAL] The sender1 is not a telemetry service.\n",
        "    apply wire as first with endpoint = sender1, managed service = monitoring service, receipt service = telemetry service\n",
    ));
    fixture.write(
        "wire/trion.trion",
        r#"package receipt-profile
namespace receipt-profile:
    system endpoint
    [SERVICE] The endpoint is a managed service that is also a receipt service.
"#,
    );
    let report = verified(&fixture);
    assert_eq!(report["conforms"], true, "{report}");
    let formula =
        contract(&report, "receipt-profile::apply-first/SERVICE")["guarantee"].to_string();
    assert!(formula.contains("monitoring service"), "{formula}");
    assert!(formula.contains("telemetry service"), "{formula}");
    assert_eq!(verdicts(&report)["consistency"], "refuted", "{report}");
}

#[test]
fn applying_a_specification_rechecks_its_mapped_refinement() {
    let fixture = project("    apply wire as first with endpoint = sender1, reply = receipt\n");
    fixture.write(
        "wire/trion.trion",
        &format!(
            "{}        detailed by [DETAIL]\n    [DETAIL] The endpoint shall send a reply.\n",
            fixture.read("wire/trion.trion"),
        ),
    );
    let positive = verified(&fixture);
    let obligation = "refinement/receipt-profile::apply-first/EMIT";
    assert_eq!(positive["conforms"], true, "{positive}");
    assert_eq!(verdicts(&positive)[obligation], "proved", "{positive}");

    fixture.write(
        "wire/trion.trion",
        &fixture.read("wire/trion.trion").replace(
            "[DETAIL] The endpoint shall send a reply.",
            "[DETAIL] The endpoint shall store a reply.",
        ),
    );
    let negative = verified(&fixture);
    assert_eq!(negative["conforms"], true, "{negative}");
    assert_eq!(verdicts(&negative)[obligation], "refuted", "{negative}");
    assert!(negative.to_string().contains("apply-first/DETAIL"));
}

#[test]
fn nested_applications_compose_mappings_and_keep_assumptions_in_their_instance() {
    let root = r#"package main
namespace main:
    refer wire
    system sender1, sender2
    environment north, south
    There is a receipt.
    The north is not a verified signal.
    The south is a verified signal.
    [NORTH-DENIAL] The sender1 shall not send the receipt.
"#;
    let fixture = Fixture::raw(&[
        (
            "trion.toml",
            "[package]\nname = \"main\"\n[dependencies]\nwire.path = \"middle\"\n",
        ),
        ("trion.trion", root),
        (
            "middle/trion.toml",
            "[package]\nname = \"middle\"\n[dependencies]\nwire.path = \"leaf\"\n",
        ),
        (
            "middle/trion.trion",
            r#"package middle
namespace middle:
    refer wire
    system sender
    environment trigger
    term payload: object
    term available signal: class
    apply wire as inner with endpoint = sender, reply = payload, switch = trigger, ready signal = available signal
"#,
        ),
        ("middle/leaf/trion.toml", "[package]\nname = \"leaf\"\n"),
        (
            "middle/leaf/trion.trion",
            r#"package leaf
namespace leaf:
    system endpoint
    environment switch
    [SIGNAL] The switch is a ready signal.
    [EMIT] The endpoint shall send a reply.
"#,
        ),
    ]);
    let reference = verified(&fixture);
    assert_eq!(reference["conforms"], true, "{reference}");
    assert_eq!(reference["applications"], serde_json::json!([]));

    let both = format!("{root}    apply wire as first with sender = sender1, payload = receipt, trigger = north, available signal = verified signal\n    apply wire as second with sender = sender2, payload = receipt, trigger = south, available signal = verified signal\n");
    fixture.write("trion.trion", &both);
    let compatible = verified(&fixture);
    assert_eq!(compatible["conforms"], true, "{compatible}");
    assert_eq!(
        verdicts(&compatible)["consistency"],
        "proved",
        "{compatible}"
    );
    assert_eq!(
        compatible["applications"][0]["nested"][0]["package"],
        "leaf"
    );
    let converted = fixture.convert(&["--json", "--out", "result"]).json();
    assert_eq!(converted["conforms"], true, "{converted}");
    let form = trioc_cli::mmt::Form::read_path(&fixture.path().join("result")).unwrap();
    assert_eq!(form.applications[0].nested[0].package, "leaf");
    let first = contract(&compatible, "leaf::apply-first/apply-inner/EMIT");
    let second = contract(&compatible, "leaf::apply-second/apply-inner/EMIT");
    assert!(first["guarantee"]
        .to_string()
        .contains("sender1|send receipt"));
    assert!(second["guarantee"]
        .to_string()
        .contains("sender2|send receipt"));

    fixture.write(
        "trion.trion",
        &format!("{both}    [SOUTH-DENIAL] The sender2 shall not send the receipt.\n"),
    );
    let conflict = verified(&fixture);
    assert_eq!(verdicts(&conflict)["consistency"], "refuted", "{conflict}");
    assert!(conflict
        .to_string()
        .contains("apply-second/apply-inner/EMIT"));
}

#[test]
fn application_preserves_the_condition_that_activates_a_source_role() {
    let fixture = project(concat!(
        "    [READY] The sender1 is not a managed service.\n",
        "    [SHAPE] The sender1 GET /broken shall send the receipt.\n",
        "    apply wire as first with endpoint = sender1, reply = receipt, ready service = managed service\n",
    ));
    fixture.write("wire/trion.trion", &format!(
        "{}\n{}",
        fixture.read("wire/trion.trion"),
        r#"    role emitter:
        activate: The $subject shall start.
        form METHOD: The $subject $operation shall $action. where $operation matches /^\/[A-Za-z_][A-Za-z0-9_.]*\/[A-Za-z_][A-Za-z0-9_]*$/ when $operation matches /^(\/|[A-Z]+ \/)/
    [ENABLE] While the endpoint is a ready service, the endpoint shall start.
"#,
    ));
    let disabled = verified(&fixture);
    assert_eq!(disabled["conforms"], true, "{disabled}");
    assert_eq!(verdicts(&disabled)["consistency"], "proved", "{disabled}");
    assert!(disabled["contracts"]
        .to_string()
        .contains("receipt-profile.emitter"));

    fixture.write(
        "trion.trion",
        &fixture
            .read("trion.trion")
            .replace("is not a managed service", "is a managed service"),
    );
    let enabled = verified(&fixture);
    assert_eq!(verdicts(&enabled)["consistency"], "refuted", "{enabled}");
    assert!(enabled.to_string().contains("apply-first/ENABLE"));
    assert!(enabled
        .to_string()
        .contains("receipt-profile.emitter::METHOD"));
}

#[test]
fn failed_refinement_reports_the_action_and_missing_state_in_its_counterexample() {
    let input = "system API\nThere is an API.\n[TOP] The status of the API shall be operational.\n    detailed by [ACT]\n[ACT] The API shall start.\n";
    let fixture = document(input);
    let report = verified(&fixture);
    assert_eq!(report["conforms"], true, "{report}");
    assert_eq!(verdicts(&report)["refinement/TOP"], "refuted", "{report}");
    let diagnosis = report["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["code"] == "detail-not-refining")
        .expect("diagnosis for the refuted refinement");
    let message = diagnosis["message"].as_str().unwrap();
    assert!(message.contains("Act(API|start@"), "{message}");
    assert!(
        message.contains("¬Val(API status@") && message.contains(", operational)"),
        "{message}"
    );
    assert!(
        message.contains("state that relation explicitly"),
        "{message}"
    );

    let repaired = document(&format!(
        "{}[STATE] The status of the API shall be operational.\n",
        input.replace("detailed by [ACT]", "detailed by [ACT], [STATE]")
    ));
    assert_eq!(verdicts(&verified(&repaired))["refinement/TOP"], "proved");
}

#[test]
fn a_referenced_form_role_applies_only_to_an_explicitly_bound_subject() {
    let manifest = format!(
        "{MANIFEST}\n[dependencies]\nwire.path = {:?}\n",
        repo_root().join("stdlib/grpc").display().to_string()
    );
    let text = r#"package main
namespace main:
    refer wire
    system API, Proxy
    The API shall use gRPC communication.
    The API GET /foo shall return a message.
    The Proxy GET /bar shall return a message.
"#;
    let fixture = Fixture::raw(&[("trion.toml", &manifest), ("trion.trion", text)]);
    let reference = verified(&fixture);
    assert_eq!(verdicts(&reference)["consistency"], "proved", "{reference}");

    fixture.write(
        "trion.trion",
        &format!("{text}    bind API as wire.service.\n"),
    );
    let applied = verified(&fixture);
    assert_eq!(verdicts(&applied)["consistency"], "refuted", "{applied}");
    assert!(applied.to_string().contains("grpc.service::METHOD-NAME"));
    assert_ne!(applied["conforms"], false, "{applied}");

    fixture.write(
        "trion.trion",
        &format!("{text}    bind API as wire.missing.\n"),
    );
    let absent = fixture.convert(&["--json"]).json();
    assert_eq!(absent["conforms"], false, "{absent}");
    assert!(absent
        .to_string()
        .contains("form role `wire.missing` is missing"));
}

#[test]
fn an_independent_requirement_has_a_counterexample() {
    let base = "system codec\n[EX] There is a codec.\n[JOB] The codec shall record the receipt.\n";
    let report = verified(&document(base));
    assert_eq!(verdicts(&report)["consistency"], "proved", "{report}");
    let contradicted = verified(&document(&format!(
        "{base}[BAD] The codec shall not record the receipt.\n"
    )));
    assert_eq!(
        verdicts(&contradicted)["consistency"],
        "refuted",
        "{contradicted}"
    );
}

#[test]
fn declared_vocabulary_needs_names_but_does_not_need_definitions() {
    let fixture = document("system codec\nThe codec is a language.\n");
    fixture.write(
        "trion.toml",
        &format!("{MANIFEST}\n[vocabulary]\nmode = \"declared\"\n"),
    );
    let report = fixture.convert(&["--json"]).json();
    assert!(
        report_codes(&report).contains(&"UNRESOLVED_TERM".to_string()),
        "{report}"
    );
    let fixture = document("system codec\nterm language: class\nThe codec is a language.\n");
    fixture.write(
        "trion.toml",
        &format!("{MANIFEST}\n[vocabulary]\nmode = \"declared\"\n"),
    );
    let report = fixture.convert(&["--json"]).json();
    assert_eq!(report["conforms"], true, "{report}");
}

#[test]
fn subset_and_existence_over_individuals_are_separate() {
    let base = "individuals guest, user\n[SUBSET] Each guest is a user.\n[USER] There is a user.\n[EMPTY] There is no guest.\n";
    let report = verified(&document(base));
    assert_eq!(
        verdicts(&report).get("compatibility").map(String::as_str),
        Some("proved"),
        "{report}"
    );
    let inclusion = contract(&report, "SUBSET")["assume"].to_string();
    assert!(
        inclusion.contains("Implies") && inclusion.contains("guest") && inclusion.contains("user"),
        "{inclusion}"
    );
    let report = verified(&document(&format!("{base}[GUEST] There is a guest.\n")));
    assert_eq!(
        verdicts(&report).get("compatibility").map(String::as_str),
        Some("refuted"),
        "{report}"
    );
}

#[test]
fn compound_membership_uses_the_same_individual_and_bound_as_separate_claims() {
    use trion_solver::{Formula, Instance, Status};

    let common = "individuals codec, schema, format, dialect\n\
                  environment codec, schema, format, dialect\n\
                  [EX] There is a codec.\n\
                  [OTHER] There is a schema.\n\
                  Each schema is a format.\n\
                  No schema is a dialect.\n";
    let compound = "[BOTH] Each codec is a format that is also a dialect.\n";
    let split = "[FORMAT] Each codec is a format.\n[DIALECT] Each codec is a dialect.\n";
    let combined = document(&format!("{common}{compound}"));
    let separated = document(&format!("{common}{split}"));
    let full = verified(&combined);
    let parts = verified(&separated);
    assert_eq!(verdicts(&full)["compatibility"], "proved", "{full}");
    assert_eq!(verdicts(&parts)["compatibility"], "proved", "{parts}");

    let assumption = |report: &Value, id| {
        let entry = contract(report, id);
        assert_eq!(entry["role"], "assumption");
        serde_json::from_value::<Formula>(entry["assume"].clone()).unwrap()
    };
    let lhs = assumption(&full, "BOTH");
    let rhs = Formula::And(vec![
        assumption(&parts, "FORMAT"),
        assumption(&parts, "DIALECT"),
    ]);
    let counterexample = Formula::Or(vec![
        Formula::And(vec![lhs.clone(), Formula::not(rhs.clone())]),
        Formula::And(vec![rhs, Formula::not(lhs)]),
    ]);
    let instance = Instance::new(&[], &[], None);
    let query = instance.add(&counterexample);
    assert_eq!(instance.decide(&[query]).status, Status::Unsatisfiable);

    let contradictory = document(&format!("{common}{compound}[BAD] No codec is a dialect.\n"));
    let report = verified(&contradictory);
    assert_eq!(verdicts(&report)["compatibility"], "refuted", "{report}");
}

#[test]
fn compound_membership_and_population_are_guarantees_of_the_declared_system_type() {
    let fixture = document(
        "individuals codec, format, dialect\n\
         system codec, format, dialect\n\
         [EX] There is a codec.\n\
         [BOTH] Each codec is a format that is a dialect.\n\
         [BAD] No codec is a dialect.\n",
    );
    let report = verified(&fixture);
    for statement in ["EX", "BOTH", "BAD"] {
        assert_eq!(
            contract(&report, statement)["role"],
            "guarantee",
            "{report}"
        );
    }
    assert_eq!(verdicts(&report)["consistency"], "refuted", "{report}");
}

#[test]
fn compound_individual_condition_and_its_subclauses_have_the_same_contract() {
    use trion_solver::{Formula, Instance, Status};

    let common = concat!(
        "individuals codec, format, dialect\n",
        "system codec, format, dialect\n",
        "There is a codec.\n",
        "Each codec is a format.\n",
        "Each codec is a dialect.\n",
    );
    let compound = "[RUN] While a codec is a format that is a dialect, the codec shall start.\n";
    let separated =
        "[RUN] While a codec is a format and the codec is a dialect, the codec shall start.\n";
    let generated = |statement: &str| verified(&document(&format!("{common}{statement}")));
    let contract_parts = |report: &Value| {
        report["contracts"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|entry| entry["statement"]["id"] == "RUN")
            .map(|entry| {
                (
                    entry["role"].clone(),
                    entry["assume"].clone(),
                    entry["guarantee"].clone(),
                )
            })
            .collect::<Vec<_>>()
    };
    let combined = generated(compound);
    let split = generated(separated);
    for report in [&combined, &split] {
        assert_eq!(report["conforms"], true, "{report}");
        assert_eq!(verdicts(report)["consistency"], "proved", "{report}");
    }
    assert!(!contract_parts(&split).is_empty(), "{split}");
    let compared = contract_parts(&combined);
    let simple = contract_parts(&split);
    assert_eq!(compared.len(), simple.len());
    let solver = Instance::new(&[], &[], None);
    for ((role, assume, guarantee), (simple_role, simple_assume, simple_guarantee)) in
        compared.into_iter().zip(simple)
    {
        assert_eq!(role, simple_role);
        for (left, right) in [(assume, simple_assume), (guarantee, simple_guarantee)] {
            let left: Formula = serde_json::from_value(left).unwrap();
            let right: Formula = serde_json::from_value(right).unwrap();
            let difference = Formula::Or(vec![
                Formula::And(vec![left.clone(), Formula::not(right.clone())]),
                Formula::And(vec![right, Formula::not(left)]),
            ]);
            let query = solver.add(&difference);
            assert_eq!(solver.decide(&[query]).status, Status::Unsatisfiable);
        }
    }
    let negative = generated(&format!("{compound}[NO] Each codec shall not start.\n"));
    assert_eq!(verdicts(&negative)["consistency"], "refuted", "{negative}");
}

#[test]
fn a_derived_class_in_an_individual_condition_expands_without_an_independent_atom() {
    let report = verified(&document(concat!(
        "individuals codec, format, dialect\n",
        "system codec, format, dialect\n",
        "Each codec is a format.\n",
        "Each codec is a dialect.\n",
        "There is a codec.\n",
        "[PORTABLE] A portable codec means a format that is a dialect.\n",
        "[RUN] While a codec is a portable codec, the codec shall start.\n",
        "[NO] Each codec shall not start.\n",
    )));
    assert_eq!(report["conforms"], true, "{report}");
    assert_eq!(verdicts(&report)["consistency"], "refuted", "{report}");
    assert!(
        report["checked"]["derivations"]["statements"]
            .as_u64()
            .unwrap()
            >= 2,
        "{report}"
    );
    let run = contract(&report, "RUN");
    assert!(!run["guarantee"].to_string().contains("portable codec"));
    assert_eq!(report["definition_expansions"]["RUN"][0]["id"], "PORTABLE");
}

#[test]
fn predicate_signatures_are_checked_in_responses_conditions_and_relative_clauses() {
    let header = "system codec\n\
                  environment gateway\n\
                  There is a message.\n\
                  There is an archive.\n\
                  alias packet = message\n\
                  predicate send(codec, message, archive)\n";
    let positive = document(&format!(
        "{header}[SEND] The codec shall send the packet to the archive within 10 ms.\n"
    ));
    let accepted = positive.convert(&["--json"]).json();
    assert_eq!(accepted["conforms"], true, "{accepted}");

    for (sentence, expected) in [
        ("The codec shall send the message.", "This use supplies 2"),
        (
            "The codec shall send the archive to the archive.",
            "argument 2",
        ),
        (
            "The gateway shall send the message to the archive.",
            "argument 1",
        ),
        (
            "When the codec sends the message to the gateway, the codec shall restart.",
            "argument 3",
        ),
        (
            "The codec shall log each message that the gateway sends to the archive.",
            "argument 1",
        ),
        (
            "The message shall be sent by the gateway to the archive.",
            "argument 1",
        ),
    ] {
        let invalid = document(&format!("{header}[BAD] {sentence}\n"));
        let report = invalid.convert(&["--json"]).json();
        assert_eq!(report["conforms"], false, "{sentence}\n{report}");
        assert!(
            report_codes(&report)
                .iter()
                .any(|code| code == "vocabulary-kind-conflict")
                && report.to_string().contains(expected),
            "{sentence}\n{report}"
        );
    }
}

#[test]
fn only_an_enumeration_closes_the_values_it_lists() {
    let base = "system mode\n[THIRD] The mode is manual.\n";
    let report = verified(&document(base));
    assert_eq!(verdicts(&report)["consistency"], "proved", "{report}");
    let report = verified(&document(&format!(
        "{base}[LIMIT] The mode is one of idle or ready.\n"
    )));
    assert_eq!(verdicts(&report)["consistency"], "refuted", "{report}");
}

#[test]
fn reference_and_mapping_changes_invalidate_the_mmt_subject() {
    let fixture = project("    apply wire as first with endpoint = sender1, reply = receipt\n");
    let read = |folder: &str| {
        let report = fixture.convert(&["--json", "--out", folder]).json();
        assert_eq!(report["conforms"], true, "{report}");
        trioc_cli::mmt::Form::read_path(&fixture.path().join(folder)).unwrap()
    };
    let first = read("first");
    let former = fixture.prove(&["first", "--json"]);
    assert_eq!(former.code, 0, "{}", former.stdout);
    fixture.write("former.json", &former.stdout);
    fixture.write(
        "trion.trion",
        &format!("{APPLICATION}    apply wire as first with endpoint = sender2, reply = receipt\n"),
    );
    let second = read("second");
    assert_ne!(first.input_digest, second.input_digest);
    assert_ne!(first.applications, second.applications);
    let stale = fixture.prove(&["second", "--against", "former.json", "--json"]);
    assert_ne!(stale.code, 0);
    assert!(
        report_codes(&stale.json())
            .iter()
            .any(|code| code == "result-stale"),
        "{}",
        stale.stdout
    );
    fixture.write(
        "wire/trion.trion",
        &fixture
            .read("wire/trion.trion")
            .replace("shall send", "shall not send"),
    );
    let revised = read("changed");
    assert_ne!(second.input_digest, revised.input_digest);
    fixture.write(
        "trion.trion",
        &fixture
            .read("trion.trion")
            .replace("refer wire", "use wire"),
    );
    let report = fixture.convert(&["--json"]).json();
    assert_eq!(report["conforms"], false, "{report}");
    assert!(
        report_codes(&report).contains(&"unresolved-import".to_string()),
        "{report}"
    );
}

#[test]
fn a_source_locator_is_evidence_alone() {
    let fixture = document(
        r#"
source WIRE:
    title "Receipt profile"
    kind citation
    locator "https://example.org/receipt-profile"
system sender
[LOCAL] The sender shall not send a receipt.
    cite WIRE
"#,
    );
    let report = verified(&fixture);
    assert_eq!(report["conforms"], true, "{report}");
    assert_eq!(verdicts(&report)["consistency"], "proved", "{report}");
    assert_eq!(report["applications"], serde_json::json!([]));
    assert_eq!(report["contracts"].as_array().unwrap().len(), 1);
}

#[test]
fn qualified_missing_exports_are_diagnosed() {
    let project = Fixture::raw(&[
        ("trion.toml", MANIFEST),
        (
            "trion.trion",
            r#"
package main
namespace main.catalog:
    The codec is a specification language.
namespace main.app:
    use main.catalog
    The main.catalog::encoder is a controlled language.
"#,
        ),
    ]);
    let report = project.convert(&["--json"]).json();
    assert!(
        report_codes(&report).contains(&"UNRESOLVED_TERM".to_string()),
        "{report}"
    );
    assert!(
        report.to_string().contains("exports no symbol named"),
        "{report}"
    );
}

#[test]
fn responsibility_follows_the_subject_under_a_condition() {
    let fixture = document(
        "system codec\nenvironment channel\n[ENV] The channel is a transport.\n[SYS] The codec is a language.\n[INPUT] While the channel is a transport, the codec shall record a message.\n[OUTPUT] While the codec is a language, the codec shall store a message.\n",
    );
    let report = fixture.convert(&["--json"]).json();
    assert_eq!(report["conforms"], true, "{report}");
    assert_eq!(contract(&report, "ENV")["role"], "assumption");
    assert_eq!(contract(&report, "SYS")["role"], "guarantee");
    assert_ne!(contract(&report, "INPUT")["assume"], "True");
    assert_eq!(contract(&report, "OUTPUT")["assume"], "True");
    assert!(contract(&report, "OUTPUT")["guarantee"]
        .to_string()
        .contains("Implies"));
}

#[test]
fn application_preserves_the_declared_responsibility() {
    let fixture = project("    apply wire as first with endpoint = sender1, reply = receipt\n");
    fixture.write(
        "trion.trion",
        &fixture.read("trion.trion").replace(
            "    system sender1, sender2",
            "    environment sender1\n    system sender2",
        ),
    );
    let report = fixture.convert(&["--json"]).json();
    assert_eq!(report["conforms"], false, "{report}");
    assert!(
        report
            .to_string()
            .contains("requires a local `system` responsibility"),
        "{report}"
    );
    assert_eq!(report["applications"], serde_json::json!([]));

    let mismatched = project("    apply wire as first with endpoint = sender1, reply = receipt\n");
    mismatched.write(
        "trion.trion",
        &mismatched
            .read("trion.trion")
            .replace("    [EX3] There is a receipt.", "    term receipt: value"),
    );
    let report = mismatched.convert(&["--json"]).json();
    assert_eq!(report["conforms"], false, "{report}");
    assert_eq!(report["applications"], serde_json::json!([]));
    assert!(
        report_codes(&report)
            .iter()
            .any(|code| code == "vocabulary-kind-conflict"),
        "{report}"
    );
    assert!(
        report
            .to_string()
            .contains("expects object but `receipt` is value"),
        "{report}"
    );
}

#[test]
fn an_alias_preserves_the_contracts_and_responsibilities() {
    let body = "system codec\nenvironment network\nprimitive codec, network\n[READY] The network status is ready.\n[RUN] When the network returns, the codec shall start.\n";
    let fixture = document(body);
    let original = fixture.read("trion.trion");
    let before = verified(&fixture);
    assert_eq!(before["conforms"], true, "{before}");
    let migrated = original
        .replace(
            "    system codec",
            "    system codec\n    alias serializer = codec",
        )
        .replace("the codec shall", "the serializer shall");
    fixture.write("trion.trion", &migrated);
    let modern = verified(&fixture);
    assert_eq!(modern["conforms"], true, "{modern}");
    for id in ["READY", "RUN"] {
        for field in ["assume", "guarantee", "role", "scope", "timing"] {
            assert_eq!(
                contract(&before, id)[field],
                contract(&modern, id)[field],
                "{id}: {field}"
            );
        }
    }
    assert_eq!(before["control"], modern["control"]);
}

#[test]
fn unused_names_and_alias_spelling_preserve_the_contracts() {
    let body = "system codec\n[TOPIC] The codec is a specification language.\n[STORE] The codec shall store the receipt.\n";
    let original = document(body).convert(&["--json"]).json();
    let unused = document(&format!(
        "{body}primitive spare\nalias serializer = codec\n"
    ))
    .convert(&["--json"])
    .json();
    assert_eq!(unused["conforms"], true, "{unused}");
    assert_eq!(original["contracts"], unused["contracts"]);
    let changed = document(&format!(
        "alias serializer = codec\n{}",
        body.replace("The codec shall", "The serializer shall")
    ))
    .convert(&["--json"])
    .json();
    assert_eq!(changed["conforms"], true, "{changed}");
    assert_eq!(
        contract(&original, "STORE")["guarantee"],
        contract(&changed, "STORE")["guarantee"]
    );

    let plural = document("system API\n[REMOVE] The API shall remove caches.\n");
    let before = plural.convert(&["--json"]).json();
    let after_text = format!(
        "{}namespace main.unused:\n    primitive caches\n",
        plural.read("trion.trion")
    );
    plural.write("trion.trion", &after_text);
    let after = plural.convert(&["--json"]).json();
    assert_eq!(after["conforms"], true, "{after}");
    assert_eq!(before["contracts"], after["contracts"]);
}

#[test]
fn applying_an_owned_relation_uses_the_mapped_arguments() {
    let fixture = project(
        "    environment cluster\n    [NO] The sender1 is not a member of the cluster.\n    apply wire as first with endpoint = sender1, network = cluster, node = member\n",
    );
    fixture.write("wire/trion.trion", "package receipt-profile\nnamespace receipt-profile:\n    system endpoint\n    environment network\n    [MEMBER] The endpoint is a node of the network.\n");
    let report = verified(&fixture);
    assert_eq!(report["conforms"], true, "{report}");
    let applied = contract(&report, "receipt-profile::apply-first/MEMBER");
    assert_eq!(applied["role"], "guarantee");
    assert!(applied["guarantee"].to_string().contains("relation member"));
    assert_eq!(
        verdicts(&report).get("consistency").map(String::as_str),
        Some("refuted"),
        "{report}"
    );
}

#[test]
fn an_untyped_population_bound_cannot_lose_its_count() {
    let fixture = document("There are 2 guests.\n");
    let report = fixture.convert(&["--json"]).json();
    assert_eq!(report["conforms"], false, "{report}");
    assert!(
        report
            .to_string()
            .contains("needs a declared finite domain"),
        "{report}"
    );
}

#[test]
fn migrated_software_spells_out_the_constraints_of_every_retained_concept() {
    let source = std::fs::read_to_string(repo_root().join("stdlib/software/trion.trion")).unwrap();
    let fixture = Fixture::raw(&[
        ("trion.toml", "[package]\nname = \"software\"\n"),
        ("trion.trion", &source),
    ]);
    let positive = verified(&fixture);
    assert_eq!(positive["conforms"], true, "{positive}");
    assert_eq!(verdicts(&positive)["compatibility"], "proved", "{positive}");

    let command = contract(&positive, "COMMAND-RUN")["assume"].to_string();
    assert!(
        command.contains("representative exists") && command.contains("person|run command by name"),
        "{command}"
    );
    let editor = contract(&positive, "EDITOR-DISPLAY")["assume"].to_string();
    assert!(editor.contains("editor|show text to person"), "{editor}");

    for (subject, denial, statement) in [
        ("program", "No computer runs the program.", "PROGRAM-RUN"),
        (
            "command",
            "No person runs the command by name.",
            "COMMAND-RUN",
        ),
        (
            "subcommand",
            "The subcommand is not a part of the command.",
            "SUBCOMMAND-PART",
        ),
        (
            "option",
            "No option changes the behavior of the command.",
            "OPTION-EFFECT",
        ),
        (
            "exit status",
            "No command returns the exit status.",
            "STATUS-RETURN",
        ),
        (
            "editor",
            "No editor shows a text to the person.",
            "EDITOR-DISPLAY",
        ),
        (
            "language server",
            "No language server serves an editor.",
            "SERVER-EDITOR",
        ),
        ("file", "No computer keeps the file.", "FILE-KEEP"),
        ("directory", "No directory has a name.", "DIRECTORY-NAME"),
        (
            "path",
            "No path locates the file.\n        No path locates the directory.",
            "PATH-LOCATES",
        ),
        (
            "digest",
            "The digest is not a SHA-256 value of the file.",
            "DIGEST-VALUE",
        ),
    ] {
        fixture.write(
            "trion.trion",
            &format!("{source}\n        There is a {subject}.\n        [DENIAL] {denial}\n"),
        );
        let result = verified(&fixture);
        assert_eq!(
            result["conforms"], true,
            "{statement} and its denial: {result}"
        );
        assert_eq!(
            verdicts(&result)["compatibility"],
            "refuted",
            "{statement} and its denial: {result}"
        );
    }
}

#[test]
fn the_self_specification_requires_a_statement_for_each_member_of_a_specification() {
    let source = std::fs::read_to_string(repo_root().join("spec/trion.trion")).unwrap();
    let revised: Vec<&str> = source
        .lines()
        .filter(|line| {
            let text = line.trim();
            text.starts_with("[SPEC-SET]") || text.starts_with("[SPEC-MEMBER]")
        })
        .collect();
    assert_eq!(revised.len(), 2);
    let check = |requirements: &str| {
        let formal = repo_root().join("stdlib/formal");
        let manifest = format!(
            "{MANIFEST}\n[dependencies]\nformal.path = {:?}\n",
            formal.to_string_lossy()
        );
        let body = format!(
            "package main\nnamespace main:\n    refer formal\n    primitive statement\n{requirements}\n    There is a specification.\n    There is a member of a specification.\n    [DENY] The member of a specification is not a statement.\n"
        );
        let fixture = Fixture::raw(&[("trion.toml", &manifest), ("trion.trion", &body)]);
        verified(&fixture)
    };
    let old = check("    A specification means a set of statements.");
    assert_eq!(old["conforms"], false, "{old}");
    assert!(
        report_codes(&old).contains(&"UNSUPPORTED_SEMANTICS".to_string()),
        "{old}"
    );
    let new = check(&revised.join("\n"));
    assert_eq!(new["conforms"], true, "{new}");
    assert_eq!(verdicts(&new)["compatibility"], "refuted", "{new}");
}

#[test]
fn migrated_formal_concepts_exclude_a_denial_of_their_classifications() {
    let library = repo_root().join("stdlib/formal");
    let source = std::fs::read_to_string(library.join("trion.trion")).unwrap();
    let fixture = Fixture::raw(&[
        ("trion.toml", "[package]\nname = \"formal\"\n"),
        ("trion.trion", &source),
    ]);
    let positive = verified(&fixture);
    assert_eq!(positive["conforms"], true, "{positive}");
    assert_eq!(verdicts(&positive)["compatibility"], "proved", "{positive}");
    for requirement in [
        "CONJUNCTION-TRUTH",
        "DISJUNCTION-TRUTH",
        "NEGATION-TRUTH",
        "CONTRACT-ASSUMPTION",
        "CONTRACT-GUARANTEE",
    ] {
        assert_eq!(contract(&positive, requirement)["role"], "assumption");
    }

    for (subject, denial) in [
        ("formula", "The formula is not a statement."),
        ("atom", "The atom is not a formula."),
        ("conjunction", "The conjunction is not a formula."),
        ("disjunction", "The disjunction is not a formula."),
        ("negation", "The negation is not a formula."),
        ("implication", "The implication is not a formula."),
        ("formula set", "The formula set is not a collection."),
        ("model", "The model is not a situation."),
        ("contract", "The contract is not a pair."),
        (
            "assumption",
            "The assumption of the contract is not a formula.",
        ),
        (
            "guarantee",
            "The guarantee of the contract is not a formula.",
        ),
        ("inference rule", "The inference rule is not a rule."),
        ("derivation", "The derivation is not a sequence."),
        ("contradiction", "The contradiction is not a formula."),
        ("proof", "The proof is not a derivation."),
        ("proof checker", "The proof checker is not a program."),
        ("calculus", "The calculus is not a set."),
    ] {
        fixture.write(
            "trion.trion",
            &format!("{source}\n        There is a {subject}.\n        [DENIAL] {denial}\n"),
        );
        let result = verified(&fixture);
        assert_eq!(
            result["conforms"], true,
            "{subject} and its denial: {result}"
        );
        assert_eq!(
            verdicts(&result)["compatibility"],
            "refuted",
            "{subject} and its denial: {result}"
        );
    }
}

#[test]
fn software_exports_its_names_separately_from_its_contracts() {
    let library = repo_root().join("stdlib/software");
    let manifest = format!(
        "{MANIFEST}\n[dependencies]\nsoftware.path = {:?}\n",
        library.display().to_string()
    );
    let body = "package main\nnamespace main:\n    refer software\n    There is a command.\n    The command is not a program.\n";
    let fixture = Fixture::raw(&[("trion.toml", &manifest), ("trion.trion", body)]);
    let reference = verified(&fixture);
    assert_eq!(reference["conforms"], true, "{reference}");
    assert_eq!(
        verdicts(&reference)["compatibility"],
        "proved",
        "{reference}"
    );
    fixture.write(
        "trion.trion",
        &body.replace("refer software", "use software"),
    );
    let imported = verified(&fixture);
    assert_eq!(imported["conforms"], true, "{imported}");
    assert_eq!(
        verdicts(&imported)["compatibility"],
        "refuted",
        "{imported}"
    );
}

#[test]
fn an_ears_reference_can_apply_its_form_to_one_subject() {
    let library = repo_root().join("stdlib/ears");
    let manifest = format!(
        "[package]\nname = \"main\"\n[dependencies]\npatterns.path = {:?}\n",
        library.display().to_string()
    );
    let input = r#"package main
namespace main:
    refer patterns
    system API, Logger
    [STOP] The API shall stop.
    [LOCAL] The Logger is idle.
"#;
    let fixture = Fixture::raw(&[("trion.toml", &manifest), ("trion.trion", input)]);
    let unbound = format!("{input}    [PERMISSION] The API may start.\n");
    fixture.write("trion.trion", &unbound);
    let reference = verified(&fixture);
    assert_eq!(reference["conforms"], true, "{reference}");
    assert_eq!(reference["applications"], serde_json::json!([]));

    fixture.write(
        "trion.trion",
        &format!("{input}    bind API as patterns.syntax.\n"),
    );
    let bound = verified(&fixture);
    assert_eq!(bound["conforms"], true, "{bound}");
    assert!(bound["contracts"].to_string().contains("ears.syntax"));
    assert!(!bound["contracts"].to_string().contains("EARS-SYNTAX"));

    fixture.write(
        "trion.trion",
        &format!("{unbound}    bind API as patterns.syntax.\n"),
    );
    let violation = fixture.convert(&["--json"]).json();
    assert_eq!(violation["conforms"], false, "{violation}");
    let refused: Vec<&Value> = violation["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|entry| entry["code"] == "syntax-not-allowed")
        .collect();
    assert_eq!(refused.len(), 1, "{violation}");
    assert_eq!(refused[0]["refs"][0]["id"], "PERMISSION");
    assert!(refused[0].to_string().contains("EARS-SYNTAX"));
}

#[test]
fn referencing_ears_keeps_its_own_source_coverage() {
    let fixture = document("refer ears\nsystem checker\n[STOP] The checker shall stop.\n");
    let library = repo_root().join("stdlib/ears");
    fixture.write(
        "trion.toml",
        &format!("{MANIFEST}\n[dependencies]\nears.path = {:?}\n", library),
    );
    let report = fixture.convert(&["--json"]).json();
    assert_eq!(report["conforms"], true, "{report}");
    assert_eq!(report["references"][0]["package"], "ears");
    assert_eq!(report["applications"], serde_json::json!([]));
    assert_eq!(report["contracts"].as_array().unwrap().len(), 1);
    assert_eq!(report["sources"]["sources"][0]["percent"], 100.0);
}
