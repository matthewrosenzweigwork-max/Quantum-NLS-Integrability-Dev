# Third-party code

Mathlib is a pinned dependency; its source is not bundled.

No sources from the Schoenflies or JordanWinding directories are included in this export.

Contour integration support includes work by Bastiaan J. Braams. See the [Lean CA Analytic Apache-2.0 license](licenses/Lean-CA-Analytic-Apache-2.0.txt).

The [complexification core](../NlsGge/ThirdConsultation/Narrative/G07C.lean) includes code from the Tau Ceti contributors, from [Complexification.lean at revision 95f09254, lines 83–354](https://github.com/TauCetiProject/TauCeti/blob/95f09254dec44b756e90d78f20f93dc4d3572783/TauCeti/Analysis/Normed/Module/Complexification.lean#L83-L354), distributed under [Apache License 2.0](licenses/TauCeti-Apache-2.0.txt). The imported core is wrapped in a local namespace with a Mathlib-only header and is followed by project-specific extensions.
