# 命題論理のローカル検証記録

基準コミットは `ef14d84`。この記録はローカル検証を対象とする。公開リリースは行っていない。最初の実装検査の対象は作業ツリーの内容識別子 `5307a8a5a1fb8a2dc7fbc0570fcad48b1a32fcf0d3aabbd127b819d91813e9c4`。以下の最初の実装検査と統合時の結果は、それぞれ当時の構成での記録。

変更分類は新しい断片の追加、同じ意味を持つ文法の拡張、厳密な後段の接続。F01〜F08 への対応は [証拠一覧](evidence-index.md) に記載した。既存の時間付き A/G 契約と MMT の入出力は既存の入口から利用する。命題論理の成果物は JSON で保存し、定義環境は `empty/1`。この選択と既存資産の分類は [設計判断 001](../decisions/001-foundation-scope.md) と [現状調査](current-architecture.md) を参照。

## 実演

リポジトリのルートで次を実行する。P はカードの有効性、Q は入場許可に対応する命題。二つの前提の下で Q が帰結し、CLI は `entails` を表示する。解析記録の検査器は元の式で全 4 付値を調べ、前提にもモデルがあることを確認する。

```sh
cargo build --locked -p trion-cli --bins
target/debug/trion formalize tests/fixtures/propositional/card.cnl > target/card.core.json
target/debug/trioc analyze target/card.core.json > target/card.analysis.json
target/debug/trioc replay target/card.analysis.json
```

保存済みの [解析記録](../../tests/fixtures/propositional/card.analysis.json) も `target/debug/trioc replay tests/fixtures/propositional/card.analysis.json` で再検査できる。命題論理の変換と解析は別コマンドに分かれる。文法第2版の言い換え `assume if P then Q.` は `--grammar propositional-cnl/2` を指定したときに同じ Core へ展開する。

`trion formalize` は Accepted のときに状態付き成果物を出力する。曖昧、未対応、不正の場合は位置付き診断と終了コード 1。 `trioc analyze` は解析記録を標準出力へ、概要を標準エラーへ出力する。未決着、前提矛盾、時間切れなどは終了コード 1。 `replay` の終了コード 0 は保存済み結果の再検査が一致したことを示す。

既定の後段・参照上限はそれぞれ 4096 付値。後段の制限時間は 5000 ms、`process-runner/1` の応答読み取り上限は 1 MiB。設定で探索を縮小した場合も、元の問いと保証範囲が記録に残る。解析ワーカーは乱数を使用しない。

## 最初の実装検査

ローカル環境は macOS arm64、Rust 1.92.0、Lean 4.35.0、Python 3.9.6。Cargo の依存関係は `Cargo.lock` で固定した。

| 検査 | コマンド | 結果 |
| --- | --- | --- |
| 命題論理モデル | Lean の定理・公理の検査 | 対象13定理に合格。空の作業ディレクトリにモデルと工具設定だけをコピーしても再検査に合格。 |
| 既存の A/G モデル | `(cd formal && lake build)` | 合格。 |
| Core 単独ビルド、禁止依存の検出 | Cargo によるビルドと当時の依存関係の検査 | 合格。実際の Cargo 依存グラフに後段依存を追加した場合は拒否。 |
| 全ワークスペースの回帰 | `PROPTEST_RNG_SEED=19 cargo test --locked --workspace --quiet` | 1,193 件合格、失敗 0 件。既存の ignore 指定 22 件。 |
| 故障注入 | 当時のソースへの変異を用いた検査 | 11 件すべてで対応する試験が失敗。強制終了、証拠の改変、限定された応答の試験もワークスペース試験に含む。 |
| CLI の実演と再生 | 上記の実演コマンド | Q の帰結と前提の整合性を確認。保存済み記録を再検査し、同じ設定で再生成した記録とのバイト一致を確認。 |

[GitHub Actions](../../.github/workflows/conformance.yml) にビルド、依存確認、証明、回帰、故障注入を登録した。ホスト環境での実行結果は未確認。

Lean の証明は M01〜M04 のモデルを対象とする。Rust の実装、シリアル化、プロセス接続は規範例、独立した照合、故障注入で確認した。元資料の意図の確認と将来の移行は [拡張規則](../../spec/propositional/extensions.trion) に従う。保証対象の詳細は [検証対象と信頼範囲](trust-boundary.md) を参照。

## trion 形式への移行時の検査

検査対象の内容識別子は `6901e9cb615fb776e7f59114363aa3313f414e66e195ca18add5afb4ed592f1c`。当時の命題論理の独立パッケージを `trion` で変換し、警告・エラーなしで MMT を生成した。`trioc prove` でトレース長・個体数を各3とする整合性と互換性の2義務が成立した。この検査は仕様文書の A/G 契約を対象とする。命題論理の定理には M01〜M04 を適用する。

- 当時の CLI と自己検証の試験は14件合格。命題論理の要求が F01〜F08 の契約を生成することも確認した。
- 命題論理の Core、参照評価、CNL、後段、解析の5クレートで `cargo test --locked` を実行し、22 件合格。
- Lean の定理と依存関係の再検査に合格。

## trion の現行仕様への統合後の検査

検査対象の内容識別子は `9b1a32a4ff0df9d30b51ed180f259546645f507a5b914ed12d960858f95ae291`。[命題論理解析](../../spec/propositional/analysis.trion)を [trion の現行仕様](../../spec/trion.trion) の一部として読み込む。成果物を再検査するときは、記録された意味論版を使う。

- `trion . --out target/current-spec-mmt` で現行仕様を変換し、`trioc prove target/current-spec-mmt` で既定の有界義務13件すべてが成立した。変換時の語彙警告1件は基準コミットでも同じだった。
- 当時の自己検証と CLI の試験は13件合格。現行仕様が F01〜F08 を読み込むことと、保存済みの解析記録を再検査できることを確認した。
- Lean で対象13定理を再検査した。

## 名称と検査方法の見直し後の検査

検査対象を示す Git のツリーは `3ac200e8101f9eff0f88655b415854fe3528465a`。この検証記録を除き、作業ツリーのファイルを一時インデックスから `git write-tree` で記録した。命題論理の保存時の意味論は `classical-propositional/1`。以前の試作形式の実演データは元の入力から再生成した。

- `trion . --out target/propositional-current-spec` と `trioc prove target/propositional-current-spec` を実行。現行仕様の有界な義務13件が成立した。
- `cargo check --locked -p trion-core` と `cargo test --locked -p trion-cli --test self_hosting --test analysis_cli` が通過した。複製先で Core に `smtlib` をビルド依存として追加すると、依存関係のテストが拒否した。
- `cargo test --locked --workspace --test adapters --test fault_injection` で9件合格。異常終了と時間切れを実際の Rust 子プロセスで確認した。
- cargo-mutants 27.1.0 の `cargo mutants` で結果受理と参照評価に作用する変異を11件選び、すべて検出した。対象は候補の照合、外部応答の分類、モデルの検査、付値の全件評価。
- `formal/` で `lake build` が通過した。命題論理モデルの定理と使用公理の確認を Lean の `#guard_msgs` に含めた。
- `PROPTEST_RNG_SEED=19 cargo test --locked --workspace --quiet` で 1,194 件合格、失敗0件。既存の ignore 指定は 22 件。
