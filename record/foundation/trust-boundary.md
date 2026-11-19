# 検証対象と信頼範囲

## ゲート1

既存の `formal/` の Lean 4.35.0 ツールチェーンで [命題論理モデル](../../formal/Trion/Propositional.lean) を検査する。`lake build` は定理と公理の一覧を照合する `#guard_msgs` も評価する。使用公理は命題外延性 `propext` と商の健全性 `Quot.sound`。信頼するのは Lean のカーネルとこの二つの公理、記述した定理が規範仕様を表すことのレビュー。

| 要件 | 対象 | 前提 |
| --- | --- | --- |
| M01 | `eval_correct`。再帰する Boolean 評価を別定義の述語と照合する | 有限木と全域付値。すべての参照は `Fin n` |
| M02 | `expand_correct`。含意の述語による意味を保存する | 整形式の表層木。文字列の解析を含まない |
| M03 | `query_condition_exact`、`translate_exact`、`target_query_exact`。全付値での反例条件と NNF の一致 | 宣言スロットを共有する全域付値。ワーカーの応答は前提にしない |
| M04 | `witness_correct`、`valuations_complete`、`valuation_count`、`empty_valuation`、`cut_off`、`exclusion_correct`、`unsat_sound`、`entails_sound` | 有限な宣言環境、全参照を含む付値、全件検査可能な予算。有限木に対する結論 |

スロット数が 0 の場合は empty_valuation と valuations_complete を適用する。評価、展開、変換、付値の生成は Lean の構造再帰で定義している。M04 の生成順は参照評価器と同じく、先頭スロットの偽の枝、真の枝の順。モデルではその順のリストとして表す。

## ゲート2

Rust の実装は Lean からの抽出コードではない。Core の式型、スロット順、検査済み文書と問いを入力処理・参照評価・アダプター間で共有する。参照評価の構造再帰と付値の列挙は、後段の NNF への変換、NNF の評価、付値の列挙と独立している。

検査に残る信頼範囲には、Rust の変換・評価・列挙がモデルに対応すること、文法、JSON とダイジェスト、依存グラフ確認、結果の受理・表示、OS のプロセス制御が含まれる。これらは適合試験と故障注入で検査する。文法の意味と元資料の意図が一致するかは、元資料の規約または確認記録に依存する。

定理の妥当性と検査器の信頼の区別についての参考資料。 [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
