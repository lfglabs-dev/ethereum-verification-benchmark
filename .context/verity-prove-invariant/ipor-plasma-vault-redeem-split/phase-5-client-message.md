Hi team,

We modeled and formally verified the public fee-charging redeem arithmetic in IPOR Fusion PlasmaVault in Verity.

The proof shows that, when the modeled instant redeem succeeds, the virtualized ERC4626 conversion PPS cannot go down. In simpler terms: the local redeem step does not make the remaining vault shares worse by this PPS measure.

We also reframed the earlier split-redeem target: split fairness is false locally, so the next meaningful question is the full buffer lifecycle, including refill/unwind costs.

Full write-up:
https://lfglabs.dev/research/ipor-plasma-vault-redeem-split

Happy to answer questions or extend coverage to the buffer lifecycle.
