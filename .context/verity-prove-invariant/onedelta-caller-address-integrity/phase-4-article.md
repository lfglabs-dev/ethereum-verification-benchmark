# Phase 4 - Article

Article branch:

- Repository: `lfglabs-dev/lfglabs.dev`
- Local clone: `/root/.sandboxed-sh/lfglabs.dev-onedelta`
- Branch: `onedelta-caller-integrity-article`

Files:

- `pages/research/onedelta-caller-address-integrity.jsx`
- `components/research/OneDeltaGuarantee.jsx`
- `public/images/logos/onedelta.svg`
- `data/research.js`

Content requirements covered:

- Public case study page.
- Metadata entry in `data/research.js`.
- Protocol logo asset.
- English specification in the guarantee component.
- Math specification with tooltip explanations matching `Specs.lean`.
- Assumptions and hypotheses for decoded commands, external-call event logs, and callback authentication precondition.
- Proof status and reproduction command.
- Links to source snapshot, docs, benchmark repository, and Lean files.

Verification:

- `npm run build` passes in `/root/.sandboxed-sh/lfglabs.dev-onedelta`.
