//! Namespace equality (`DPath`, MMT's `DPath.equals`: the scheme is ignored,
//! an absent and an empty authority are equal, a trailing slash is ignored)
//! is an equivalence, and `Ord` and `Hash` agree with it, over generated URIs
//! that differ exactly in those respects.

mod common;

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use common::cases;
use mmt::uri::{DPath, Uri};
use proptest::prelude::*;

fn namespace() -> impl Strategy<Value = DPath> {
    let scheme = prop::sample::select(vec!["http://", "https://", "file://", "file:", "", "scala://"]);
    let authority = prop::sample::select(vec!["", "a.org", "b.org"]);
    let segments = prop::collection::vec(prop::sample::select(vec!["x", "y", ""]), 0..3);
    (scheme, authority, any::<bool>(), segments, any::<bool>()).prop_filter_map("not a namespace", |(scheme, authority, slash, segments, trailing)| {
        let mut s = format!("{scheme}{authority}");
        if slash || !authority.is_empty() {
            s.push('/');
        }
        s.push_str(&segments.join("/"));
        if trailing {
            s.push('/');
        }
        DPath::new(Uri::parse(&s)).ok()
    })
}

fn hash(d: &DPath) -> u64 {
    let mut h = DefaultHasher::new();
    d.hash(&mut h);
    h.finish()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(cases(4096)))]

    #[test]
    fn equality_is_an_equivalence_and_order_and_hash_agree(x in namespace(), y in namespace(), z in namespace()) {
        prop_assert_eq!(&x, &x);
        prop_assert_eq!(x == y, y == x, "{} {}", x, y);
        if x == y && y == z {
            prop_assert_eq!(&x, &z);
        }
        prop_assert_eq!(x == y, x.cmp(&y) == std::cmp::Ordering::Equal, "{} {}", x, y);
        prop_assert_eq!(x.cmp(&y), y.cmp(&x).reverse());
        if x < y && y < z {
            prop_assert!(x < z, "{} {} {}", x, y, z);
        }
        if x == y {
            prop_assert_eq!(hash(&x), hash(&y), "{} {}", x, y);
        }
    }
}

#[test]
fn the_reported_counterexamples_hold() {
    let d = |s: &str| DPath::new(Uri::parse(s)).unwrap();
    // file:// and / were equal in one direction only
    assert_eq!(d("file:///") == d("/"), d("/") == d("file:///"));
    // http://a.org/x == https://a.org/x but http://a.org/x < http://a.org/y < https://a.org/x
    assert_eq!(d("http://a.org/x"), d("https://a.org/x"));
    assert!(d("http://a.org/x") < d("http://a.org/y"));
    assert!(d("https://a.org/x") < d("http://a.org/y"));
}
