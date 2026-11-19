# 命題論理解析の証拠一覧

対象スナップショットと実行結果は [ローカル検証記録](propositional-verification.md) に記す。規範の定義、Lean で検査した命題、Rust の適合試験はそれぞれ根拠が異なる。対象と残る信頼範囲は [検証対象と信頼範囲](trust-boundary.md) を参照。

| 要件 | 規範定義と機械検査 | 適合試験と検出する故障 |
| --- | --- | --- |
| F01 版付きの規範意味論 | [Core](../../spec/propositional/core.trion)、[問い](../../spec/propositional/queries.trion)。M01 と M02 を機械検査 | [規範例](../../tests/adapters/boolean.rs) と [文法試験](../../tests/grammar/propositional.rs)。含意の前件・後件を逆にすると不一致。 |
| F02 閉じた正式構造 | [整形式と保存](../../spec/propositional/core.trion)。Lean の `Expr n` と `Fin n` で対象を限定 | [Core 適合試験](../../tests/conformance/core.rs)。未知構成子、余分なペイロード、表外の参照、破損、重複を拒否。 |
| F03 独立した Core | [設計判断](../decisions/001-foundation-scope.md)、[拡張規則](../../spec/propositional/extensions.trion) | [Cargo の依存グラフ](../../crates/trion-cli/tests/self_hosting.rs) と [交換演習](../../tests/architecture/propositional.rs)。禁止された後段依存、対応範囲を無視した変換を検出。 |
| F04 前提と問いの追跡 | [問い](../../spec/propositional/queries.trion)、[結果](../../spec/propositional/results.trion)、[CNL の対応情報](../../spec/propositional/grammar.trion) | [CLI](../../crates/trion-cli/tests/analysis_cli.rs) と [故障注入](../../tests/fault-injection/analysis.rs)。前提を混ぜた文書、別の問い・前提の応答を拒否。 |
| F05 変換の条件と保存 | [変換契約](../../spec/propositional/translation.trion)。M03 を機械検査 | [独立照合](../../tests/adapters/boolean.rs)、[交換演習](../../tests/architecture/propositional.rs)、[故障注入](../../tests/fault-injection/analysis.rs)。制約の欠落と能力の不足を検出。 |
| F06 結論を根拠と照合 | [結果](../../spec/propositional/results.trion)。M04 を機械検査 | [結果受理試験](../../tests/adapters/boolean.rs)、[故障注入](../../tests/fault-injection/analysis.rs)、[CLI](../../crates/trion-cli/tests/analysis_cli.rs)。誤った候補、前提矛盾、unknown、途中終了、時間切れ、範囲欠落を検査。 |
| F07 固定版と再検査 | [保存](../../spec/propositional/core.trion)、[拡張規則](../../spec/propositional/extensions.trion) | [版固定](../../tests/grammar/propositional.rs) と [再検査](../../crates/trion-cli/tests/analysis_cli.rs)。旧版解釈の変更、版違い、変換・証拠の改変を拒否。 |
| F08 保証範囲 | [検証対象と信頼範囲](trust-boundary.md)、[変換契約](../../spec/propositional/translation.trion)、[結果](../../spec/propositional/results.trion) | [Lean の再検査](../../formal/Trion/Propositional.lean)、[限定応答の注入](../../tests/fault-injection/analysis.rs)、[ローカル検証記録](propositional-verification.md)。 |

## M01–M04

[Lean モデル](../../formal/Trion/Propositional.lean)の定理、公理、検査対象は [検証対象と信頼範囲](trust-boundary.md) に記載した。M04 の付値生成については、3 命題で各付値だけが唯一の証人になる例と、0 命題で空付値だけが証人になる例を実装でも試した。 [Core 適合試験](../../tests/conformance/core.rs)

独立照合では、命題数 0〜4、式の深さ最大 5、前提数 0〜3、各命題数で 32 ケースを種 `0x8af7_239b_0061_c45d` から生成する。定数、宣言済み参照、否定、論理積、論理和を使い、充足可能性と帰結を交互に選ぶ。全付値で前提を固定した小問でも後段と参照評価を照合し、名前を一貫して変更した場合も比較する。手計算例は含意とその逆、矛盾、空付値を別に保持する。生成器と検査する性質を分ける設計を参照した。 [試験コード](../../tests/adapters/boolean.rs) · [QuickCheck 原論文](https://research.chalmers.se/en/publication/237427)

## 完成判定

| 第15節の項目 | 根拠 |
| --- | --- |
| F01〜F08、全構成子と整形式性 | 上表、[仕様の自己検査](../../crates/trion-cli/tests/self_hosting.rs)、[Core 規範仕様](../../spec/propositional/core.trion) |
| M01〜M04、前提と使用公理 | [Lean モデル](../../formal/Trion/Propositional.lean) と [信頼範囲](trust-boundary.md) |
| 配備する CLI と独立評価、Core の依存 | [CLI 一貫試験](../../crates/trion-cli/tests/analysis_cli.rs)、[生成照合](../../tests/adapters/boolean.rs)、[依存方向](../../crates/trion-cli/tests/self_hosting.rs) |
| 前提、問い、変換、証拠、範囲の追跡 | [CLI 一貫試験](../../crates/trion-cli/tests/analysis_cli.rs) と [F04〜F07 の試験](../../tests/fault-injection/analysis.rs) |
| 曖昧、未対応、未決着、矛盾、障害 | [文法試験](../../tests/grammar/propositional.rs)、[結果試験](../../tests/adapters/boolean.rs)、[強制終了と時間切れ](../../tests/fault-injection/analysis.rs) |
| 重大な故障を個別に検出 | [故障入力の試験](../../tests/fault-injection/analysis.rs)、[依存関係の検査](../../crates/trion-cli/tests/self_hosting.rs)、[cargo-mutants による照合](propositional-verification.md) |
| 文法追加と制限された後段への交換 | [交換演習](../../tests/architecture/propositional.rs) |
| 版の固定、証拠の再検査、移行 | [保存仕様](../../spec/propositional/core.trion)、[移行規則](../../spec/propositional/extensions.trion)、[版固定の回帰](../../tests/grammar/propositional.rs) |
| 未定義の図表・擬似コードを扱わない | [図表の入口](../../spec/propositional/extensions.trion) と [構文・構造の拒否例](../../tests/grammar/propositional.rs) |
| モデルの証明、適合試験、元資料の確認 | [信頼範囲](trust-boundary.md) と [出所の契約](../../spec/propositional/extensions.trion) |
| 同一スナップショットに結び付いた証拠 | [Git の検証対象とローカル検証記録](propositional-verification.md) |
