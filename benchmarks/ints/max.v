From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


Definition max : val :=
rec: "max" "r" "x" "y" :=
if: "y" ≤ "x"
then (
("r") <- ("x");; 
#()
)
else (
("r") <- ("y");; 
#()
).


Lemma max_spec :
∀ (r : loc) (x : Z) (y : Z),
{{{ r ↦ #0 }}}
  max #r #x #y
{{{ RET #(); ∃ (m : Z), ⌜(x ≤ m)%Z ∧ (y ≤ m)%Z⌝ ∗ r ↦ #m }}}.
Proof.
iIntros (r x y ϕ) "iH1 Post".
iRewriteHyp.
iLöb as "max" forall (r x y ϕ).
ssl_begin.
ssl_if iH2.
ssl_store.
try wp_pures.
iFindApply.
iExists x.
ssl_finish.

ssl_store.
try wp_pures.
iFindApply.
iExists y.
ssl_finish.
Qed.
