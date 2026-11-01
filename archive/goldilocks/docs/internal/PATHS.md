# Archived source coordinates

The archive preserves historical bytes, source fragments and absolute workstation paths.
Old library coordinates resolve through the table below. This is a navigation index.
It does not make stale literal links inside historical documents work automatically.
The sole machine mapping is [lakefile.toml](../../lakefile.toml).

| Historical library prefix | Group / current sources |
| --- | --- |
| `AvailableChainEngineV2` | [engine / tree][2] · [facade][f2] |
| `AvailableChainFGCompose` | [generic / tree][3] · [facade][f3] |
| `AvailableChainFGSA` | [fgsa / tree][4] · [facade][f4] |
| `AvailableChainFGSAClaims` | [fgsa / tree][5] · [facade][f5] |
| `AvailableChainFGSAInhabit` | [fgsa / tree][6] · [facade][f6] |
| `AvailableChainFGSAProofs` | [fgsa / tree][7] · [facade][f7] |
| `AvailableChainFGSARun` | [fgsa / tree][8] · [facade][f8] |
| `AvailableChainFramework` | [engine / tree][9] · [facade][f9] |
| `AvailableChainGeneric` | [generic / tree][10] · [facade][f10] |
| `AvailableChainGridCO` | [legacy / tree][11] · [facade][f11] |
| `AvailableChainKit` | [generic / tree][12] · [facade][f12] |
| `AvailableChainKitFG` | [generic / tree][13] · [facade][f13] |
| `AvailableChainKitV2` | [generic / tree][14] · [facade][f14] |
| `AvailableChainLStar` | [legacy / tree][15] · [facade][f15] |
| `AvailableChainModel` | [engine / tree][16] · [facade][f16] |
| `AvailableChainPCSA` | [pcsa / tree][17] · [facade][f17] |
| `AvailableChainPCSAClaims` | [pcsa / tree][18] · [facade][f18] |
| `AvailableChainPCSAProofs` | [pcsa / tree][19] · [facade][f19] |
| `AvailableChainPCSARun` | [pcsa / tree][20] · [facade][f20] |
| `AvailableChainRegistry` | [engine / tree][21] · [facade][f21] |
| `AvailableChainSA` | [legacy / tree][22] · [facade][f22] |
| `AvailableChainSAPC` | [legacy / tree][23] · [facade][f23] |
| `AvailableChainSimplexFG` | [legacy / tree][24] · [facade][f24] |
| `AvailableChainStatements` | [engine / tree][25] · [facade][f25] |
| `AvailableChainWitnesses` | [engine / tree][26] · [facade][f26] |

For `AvailableChainX/A/B.lean`, follow that library tree to `A/B.lean`.
Namespaces, module identities and relative paths inside each library are unchanged.
The executable resolver can print an exact source path from a module name:

```sh
python3 -B scripts/source_layout.py path AvailableChainFGSAClaims.FGSAClaims
python3 -B scripts/source_layout.py --revision ae5dc168 path AvailableChainFGSAClaims.FGSAClaims
```

Every former `docs/<path>` artefact is now at `docs/internal/<path>`, with its relative
subtrees and provenance preserved. The reader docs in `docs/` are separate documents.
The old `docs/ARCHITECTURE.md` is [the session map](ARCHITECTURE.md).
The referenced `plans/2026-09-29-fgsa-composition-t7-t1.md` was already absent at the base.

[2]: ../../engine/AvailableChainEngineV2/
[f2]: ../../engine/AvailableChainEngineV2.lean
[3]: ../../generic/AvailableChainFGCompose/
[f3]: ../../generic/AvailableChainFGCompose.lean
[4]: ../../fgsa/AvailableChainFGSA/
[f4]: ../../fgsa/AvailableChainFGSA.lean
[5]: ../../fgsa/AvailableChainFGSAClaims/
[f5]: ../../fgsa/AvailableChainFGSAClaims.lean
[6]: ../../fgsa/AvailableChainFGSAInhabit/
[f6]: ../../fgsa/AvailableChainFGSAInhabit.lean
[7]: ../../fgsa/AvailableChainFGSAProofs/
[f7]: ../../fgsa/AvailableChainFGSAProofs.lean
[8]: ../../fgsa/AvailableChainFGSARun/
[f8]: ../../fgsa/AvailableChainFGSARun.lean
[9]: ../../engine/AvailableChainFramework/
[f9]: ../../engine/AvailableChainFramework.lean
[10]: ../../generic/AvailableChainGeneric/
[f10]: ../../generic/AvailableChainGeneric.lean
[11]: ../../legacy/AvailableChainGridCO/
[f11]: ../../legacy/AvailableChainGridCO.lean
[12]: ../../generic/AvailableChainKit/
[f12]: ../../generic/AvailableChainKit.lean
[13]: ../../generic/AvailableChainKitFG/
[f13]: ../../generic/AvailableChainKitFG.lean
[14]: ../../generic/AvailableChainKitV2/
[f14]: ../../generic/AvailableChainKitV2.lean
[15]: ../../legacy/AvailableChainLStar/
[f15]: ../../legacy/AvailableChainLStar.lean
[16]: ../../engine/AvailableChainModel/
[f16]: ../../engine/AvailableChainModel.lean
[17]: ../../pcsa/AvailableChainPCSA/
[f17]: ../../pcsa/AvailableChainPCSA.lean
[18]: ../../pcsa/AvailableChainPCSAClaims/
[f18]: ../../pcsa/AvailableChainPCSAClaims.lean
[19]: ../../pcsa/AvailableChainPCSAProofs/
[f19]: ../../pcsa/AvailableChainPCSAProofs.lean
[20]: ../../pcsa/AvailableChainPCSARun/
[f20]: ../../pcsa/AvailableChainPCSARun.lean
[21]: ../../engine/AvailableChainRegistry/
[f21]: ../../engine/AvailableChainRegistry.lean
[22]: ../../legacy/AvailableChainSA/
[f22]: ../../legacy/AvailableChainSA.lean
[23]: ../../legacy/AvailableChainSAPC/
[f23]: ../../legacy/AvailableChainSAPC.lean
[24]: ../../legacy/AvailableChainSimplexFG/
[f24]: ../../legacy/AvailableChainSimplexFG.lean
[25]: ../../engine/AvailableChainStatements/
[f25]: ../../engine/AvailableChainStatements.lean
[26]: ../../engine/AvailableChainWitnesses/
[f26]: ../../engine/AvailableChainWitnesses.lean
