import WeakSchur

#print WeakSchur.ModularWitness
#print WeakSchur.weakSchur
#print WeakSchur.firstBad
#print WeakSchur.roomCut
#print WeakSchur.boundaryHit
#check @WeakSchur.one_colour_threshold
#check @WeakSchur.weakSchur_isGreatest
#print axioms WeakSchur.tri_closed
#print axioms WeakSchur.signed_iff_witness
#print axioms WeakSchur.spectrum_one
#print axioms WeakSchur.spectrum_small
#print axioms WeakSchur.spectrum_tight
#print axioms WeakSchur.spectrum_room
#print axioms WeakSchur.hasSolution_iff_firstBad
#print axioms WeakSchur.hasSolution_iff_modularWitness
#print axioms WeakSchur.one_colour_threshold
#print axioms WeakSchur.weakSchur_isGreatest

example : WeakSchur.weakSchur 6 4 = 5 := by decide
example : WeakSchur.weakSchur 11 4 = 4 := by decide
example : WeakSchur.weakSchur 23 4 = 7 := by decide
