# 着手時の構成調査

調査基準は `ef14d84`。表は調査時点の構成を記録する。命題論理の期待値は現行仕様の [意味と保存の定義](../../spec/propositional/core.trion) から導く。

| 資産 | 現行の入口と責務 | 取り扱い |
| --- | --- | --- |
| `AGENTS.md`、`spec/*.trion`、`spec/semantics/`、`spec/patterns/ledger.toml` | trion の A/G 契約、責任分界、時間と個体の読み、パターン台帳 | 保持。命題論理解析の要求は現行仕様に組み込んだ。 |
| `formal/Trion/`、`formal/Oracle.lean` | 契約集合、マージ、文展開、文書健全性と展開のオラクル。Lean 4.35.0 | 保持。ツールチェーンの選択を再利用し、命題論理解析 の意味モデルを独立に検査する。 |
| `trion-language` | `document.rs` と `syntax/` が入力を処理し、`reading/` が意味を読み、`trion-solver::Formula` を利用する | 隔離。この依存方向を Core に持ち込むと F03 に反する。 |
| `trion-solver`、`trion-verification` | 算術・量化・証明探索、責任・時間・構造の解析、証明義務および形式別出力 | 保持。命題論理解析 には小さい別の変換契約を設ける。 |
| `trion-checker` | `eval.rs` の具体挙動の検査や `derive.rs` の読みの再検査。既存の言語型・式型を利用する | 保持。命題論理解析 の参照評価には既存の判定本体を共有しない。 |
| `trion-cli`、`trioc-cli`、`mmt` | `trion --out` が MMT と文書へ変換し、`trioc prove` が義務ごとに判定・証明形式を出す | 保持。命題論理解析の入口と保存形式を追加する。 |
| `smtlib`、`alethe`、`cpc`、`eunoia`、`moxi` | 後段形式の構文・検査のライブラリーと外部検査器のテスト | 隔離。命題論理解析 の証拠は元の式で再検査する。 |
| `stdlib/`、`editors/`、`trion-lsp` | 語彙集、エディタ統合、言語サーバー | 保持。編集機能の追加は今回の範囲外。 |
| Rust 各クレートの `tests/`、`formal/lakefile.lean` | 既存の契約・読解・証明形式の回帰、Lean ビルド。追跡済み CI 定義は調査時点でなし | 保持。命題論理解析 の適合試験と依存方向の CI を追加する。 |

依存は `cargo tree --workspace --locked --depth 1 -e normal`、入口は各ライブラリーと CLI のソース、形式モデルは `cd formal && lake build` で確認した。既存の全パターンを 命題論理解析 の受入条件で再審査する作業、既存 MMT と 命題論理解析 の相互変換、エディタの手動確認は今回の調査対象外。回帰試験の結果は [ローカル検証記録](propositional-verification.md) を参照。
