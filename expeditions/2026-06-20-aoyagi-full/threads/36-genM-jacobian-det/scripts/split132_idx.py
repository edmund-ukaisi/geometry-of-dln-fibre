# split132: reg = coord 0; after piFinSuccAbove 0 on Fin 9 -> Fin 8 where original coord k>0 -> k-1.
# core {3,4} -> Fin-8 indices {2,3}. So coreSpec132 pulls {2,3} from Fin 8.
# peel Fin-8 index 2 (orig 3) -> Fin 7 where >2 shifts down; then orig 4 was Fin-8 idx 3 -> Fin-7 idx 2.
# So: piFinSuccAbove 2 on Fin 8, then piFinSuccAbove 2 on Fin 7. (vs (2,3,1): {5,6} -> peel 5,5)
orig_core = [3,4]
after_peel0 = [k-1 for k in orig_core]   # remove index 0
print("core in Fin 8 (after peel coord 0):", after_peel0)   # expect [2,3]
# peel first core elem (Fin-8 idx 2): Fin 7, remaining core elem 3 -> 3-1=2
print("second core elem in Fin 7 (after peel idx 2):", after_peel0[1]-1)  # expect 2
# spec = {1,2,5,6,7,8} (orig), 6 coords. In base231 we reconstruct via base132.
# base132 q (reg=q.1 0 = coord0; spec q.2 = coords 1,2,5,6,7,8): put 0 at core slots 3,4.
# base132 = [q.1 0, q.2 0, q.2 1, 0, 0, q.2 2, q.2 3, q.2 4, q.2 5]
#   coord0=reg, coord1=spec0, coord2=spec1, coord3=0,coord4=0, coord5=spec2,...,coord8=spec5
print("base132 layout: [reg, spec0, spec1, 0, 0, spec2, spec3, spec4, spec5]")
print("  i.e. coords 1,2 -> spec 0,1 ; coords 5,6,7,8 -> spec 2,3,4,5")
