# P-As Round 9 — remaining work

Status: ASSEMBLY CLOSED / MANIFEST BLOCKED-PCSA. Base 082d9c89; branch sleep-pas9.
All 68 assigned targets are GREEN. No P-As proof obligation remains.

The four explicit per-run inputs from Round 8 now have named recovery producers.
Assembly supplies the full Foundation telescope. HTimeClaim and fgsaClaims
have no added claim premise. Public Claims/Statements and Proofs/Healing are unchanged.
The finite witness, local horizon and complete recoveryStart budget stay in place.

The fixture restore-time ports are already present in the merged base and pass
source checks. Eight obsolete Outage audit references are removed. The current
scoped producers remain covered. Canonical coverage corrects 14 moved proof
owners, adds four existing witness and Root rows and four Assembly adapters, and removes
36 misplaced test rows. The six local test audits check those test commands.

Exact producers, public premises and final validation:
[P-As.round9-handoff.md](P-As.round9-handoff.md).
Evidence: .lake/sleep-pas-r9/. Round 8 blockers are historical context only.
The full manifest's claims stage imports PC-SA. It stops on missing PC-SA proof
artifacts. Building those prerequisites fails in unchanged
AvailableChainPCSARun/Model/Protocol.lean:449: restore lacks the new Time argument.
A PC-SA protocol port is needed before the unchanged full manifest can pass.
Its later snapshot controls have not run. Global P23, G-S2, exposure policy and
release work remain with the lead.
