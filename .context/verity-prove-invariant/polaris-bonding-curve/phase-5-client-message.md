Hi team,

Good news: we modeled and formally verified a Polaris Finance bonding-curve checkpoint invariant in Verity.

The proof shows that modeled successful init establishes, and modeled successful buy, sell, and fee-router floor-burn paths preserve, the two stored reserve checkpoints, with PRB/ABDK fixed-point pow kept as an explicit linked boundary. In simpler terms: these modeled paths keep the stored pricing checkpoints aligned with the curve state used for the invariant.

Full write-up here:
https://lfglabs.dev/research/polaris-bonding-curve-reserve-ratio

Happy to answer questions or to explore how we can extend formal verification coverage on the rest of Polaris.
