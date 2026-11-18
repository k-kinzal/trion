//! Character classes as MMT uses them.
//!
//! MMT classifies characters with `java.lang.Character` (`api/parser/Reader.scala`,
//! `api/parser/TokenList.scala`): whitespace is `Character.isWhitespace`,
//! letters are the general categories L*, numbers are Nd and Nl (not No, so
//! that superscript digits can be operators), marks are Mn, Mc and Me, and
//! connectors are Pc. The Rust standard library has no general-category
//! tables, so this module derives the classes from `char::is_alphabetic` and
//! `char::is_numeric` and corrects them by explicit tables of the marks, letter
//! numbers and other numbers in the blocks that occur in mathematical text
//! (Latin, Greek, combining diacritics, letterlike symbols, number forms,
//! enclosed alphanumerics). Characters outside those tables are classified by
//! the standard library's properties, which may differ from Java's categories
//! in rare scripts; characters outside the Basic Multilingual Plane, which
//! Java stores as two UTF-16 units, are treated as letters.

/// `Character.isWhitespace` of Java.
pub fn is_java_whitespace(c: char) -> bool {
    matches!(c,
        '\t' | '\n' | '\u{0B}' | '\u{0C}' | '\r' | '\u{1C}'..='\u{1F}' | ' ' | '\u{1680}'
        | '\u{2000}'..='\u{2006}' | '\u{2008}'..='\u{200A}' | '\u{2028}' | '\u{2029}' | '\u{205F}' | '\u{3000}')
}

/// Combining marks (Mn, Mc, Me) in the blocks covered by the tables.
pub fn is_mark(c: char) -> bool {
    matches!(c,
        '\u{0300}'..='\u{036F}' | '\u{0483}'..='\u{0489}' | '\u{0591}'..='\u{05BD}' | '\u{05BF}' | '\u{05C1}' | '\u{05C2}'
        | '\u{05C4}' | '\u{05C5}' | '\u{05C7}' | '\u{0610}'..='\u{061A}' | '\u{064B}'..='\u{065F}' | '\u{0670}'
        | '\u{0900}'..='\u{0903}' | '\u{093A}'..='\u{094F}' | '\u{1AB0}'..='\u{1AFF}' | '\u{1DC0}'..='\u{1DFF}'
        | '\u{20D0}'..='\u{20FF}' | '\u{302A}'..='\u{302F}' | '\u{3099}' | '\u{309A}' | '\u{FE00}'..='\u{FE0F}' | '\u{FE20}'..='\u{FE2F}')
}

/// Letter numbers (Nl).
fn is_letter_number(c: char) -> bool {
    matches!(c, '\u{16EE}'..='\u{16F0}' | '\u{2160}'..='\u{2182}' | '\u{2185}'..='\u{2188}' | '\u{3007}' | '\u{3021}'..='\u{3029}' | '\u{3038}'..='\u{303A}' | '\u{A6E6}'..='\u{A6EF}')
}

/// Other numbers (No), which Java does not treat as numbers here.
fn is_other_number(c: char) -> bool {
    matches!(c,
        '\u{00B2}' | '\u{00B3}' | '\u{00B9}' | '\u{00BC}'..='\u{00BE}' | '\u{09F4}'..='\u{09F9}' | '\u{0BF0}'..='\u{0BF2}'
        | '\u{0F2A}'..='\u{0F33}' | '\u{1369}'..='\u{137C}' | '\u{17F0}'..='\u{17F9}' | '\u{19DA}' | '\u{2070}' | '\u{2074}'..='\u{2079}'
        | '\u{2080}'..='\u{2089}' | '\u{2150}'..='\u{215F}' | '\u{2189}' | '\u{2460}'..='\u{249B}' | '\u{24EA}'..='\u{24FF}'
        | '\u{2776}'..='\u{2793}' | '\u{2CFD}' | '\u{3192}'..='\u{3195}' | '\u{3220}'..='\u{3229}' | '\u{3248}'..='\u{324F}'
        | '\u{3251}'..='\u{325F}' | '\u{3280}'..='\u{3289}' | '\u{32B1}'..='\u{32BF}')
}

/// Connector punctuation (Pc).
pub fn is_connector(c: char) -> bool {
    matches!(c, '_' | '\u{203F}' | '\u{2040}' | '\u{2054}' | '\u{FE33}' | '\u{FE34}' | '\u{FE4D}'..='\u{FE4F}' | '\u{FF3F}')
}

/// `Character.isLetter` of Java (general categories L*).
pub fn is_letter(c: char) -> bool {
    if (c as u32) > 0xFFFF {
        return true;
    }
    c.is_alphabetic() && !is_mark(c) && !is_letter_number(c) && !is_number_like_alphabetic(c)
}

/// Characters that Rust's Alphabetic property includes but that are not letters
/// (Other_Alphabetic marks outside the mark table are not corrected).
fn is_number_like_alphabetic(c: char) -> bool {
    matches!(c, '\u{0345}')
}

/// MMT's numbers: Java's DECIMAL_DIGIT_NUMBER and LETTER_NUMBER.
pub fn is_number(c: char) -> bool {
    if is_letter_number(c) {
        return true;
    }
    c.is_numeric() && !is_other_number(c)
}

/// Letter or number.
pub fn is_letter_or_number(c: char) -> bool {
    is_letter(c) || is_number(c)
}

/// `TokenList.canFollow`: true if there is no word break between the two characters.
pub fn can_follow(before: char, after: char) -> bool {
    !is_java_whitespace(after) && (is_connector(before) || is_connector(after) || (is_letter_or_number(before) == is_letter_or_number(after)))
}

/// Java's `Character.isDigit` restricted to what MMT's number lexer needs.
pub fn is_digit(c: char) -> bool {
    c.is_ascii_digit() || (c.is_numeric() && !is_other_number(c) && !is_letter_number(c))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classes_of_common_characters() {
        assert!(is_letter('a') && is_letter('ℕ') && is_letter('α'));
        assert!(!is_letter('⟶') && !is_letter('⊦') && !is_letter('…'));
        assert!(is_number('7') && !is_number('²'));
        assert!(is_connector('_'));
        assert!(is_mark('\u{0338}'));
        assert!(is_java_whitespace(' ') && !is_java_whitespace('\u{00A0}'));
        assert!(can_follow('a', 'b') && can_follow('a', '_') && !can_follow('a', '+') && can_follow('+', '+'));
    }
}
