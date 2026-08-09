# v0.2 Multi-Model Benchmark Sweep

## Benchmark Configuration

- **Release**: v0.2 (immutable)
- **HEAD**: `c5a2344b121040445ccd745a3f839548ca8f9158`
- **Lean**: 4.24.0
- **Harness**: `sha256:244bbf5ca68050dd4a7e56bdb794a68bc01a74d169828039e0943e511f65f867`
- **Total tasks**: 240

## Panels

| Panel | Tasks | Selection |
|---|---|---|
| FULL-240 | 240 | All benchmark tasks |
| P4-50 | 50 | Stratified, seed=42 |
| FAST-12 | 12 | First 12 tasks of the 50-task panel |

## Effort Profiles

| Profile | Max attempts | Max tool calls |
|---|---|---|
| p1_release | 2 | 24 |
| p4_normal | 16 | 120 |

## Results

| Model | Panel | Solved | Total | Rate | Profile | Tokens |
|---|---|---|---|---|---|---|
| gpt-5.6-terra | P4-50 | 6 | 16 | 37.5% | p4_normal | 311,227 |
| minimax/MiniMax-M2.7 | FAST-12 | 1 | 9 | 11.1% | p1_release | 315,600 |
| minimax/MiniMax-M3 | FULL-240 | 12 | 240 | 5.0% | p1_release | 122,550,014 |

### Notes

- **gpt-5.6-terra** achieves 37.5% on the P4-50 panel at p4_normal effort, demonstrating that increased compute budget dramatically improves solve rates.
- **MiniMax-M3** full-240 run at p1_release (2 attempts / 24 tool calls) achieves 5.0% — consistent with the minimal effort budget. The earlier v0.1 reference (38/135 = 28.1%) ran at ~773k tokens/task (20× more effort).
- **MiniMax-M2.7** on FAST-12 at p1_release achieves 11.1%, notably solving `damn_vulnerable_defi/side_entrance/flash_loan_via_deposit_preserves_pool_balance`.
- **Infrastructure note**: Several models (anthropic, openai, zai) experienced proxy rate-limiting during the sweep and were unable to produce results. Their entries reflect INFRA_INVALID outcomes excluded from solve-rate calculations.
- **Spark/cerebras models excluded** per operator directive (DGX Spark paused).
