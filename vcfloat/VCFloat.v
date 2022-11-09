From vcfloat Require Export FPLang FPLangOpt RAux Rounding Reify Float_notations Automate Prune.
Set Bullet Behavior "Strict Subproofs".

Ltac CheckBound x hi :=
     idtac "Checking that" x "is indeed less than" hi;
       exact (Binary.Bcompare _ _ ltac:(ShowBound (proj1_sig x)) hi = Some Lt).
