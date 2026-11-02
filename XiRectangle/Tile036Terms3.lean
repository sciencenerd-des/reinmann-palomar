/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile036Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨36,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8601/640)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((7/8), (8601/640))
  have he : value ((7/8), (8601/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-45376701/16777216), (-348468755/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-921655777867977/18014398509481984), (194078224872167/4503599627370496)), (221341289/18014398509481984), by norm_num⟩
  | 1 => ⟨((679225239/4294967296), (-143028267/1073741824)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-1049757025/4294967296), (884212891/4294967296)), (1/16777216), by norm_num⟩
  | 3 => ⟨((540807255/2147483648), (-7117551/33554432)), (133/2147483648), by norm_num⟩
  | 4 => ⟨((-208957273/1073741824), (352010437/2147483648)), (207/4294967296), by norm_num⟩
  | 5 => ⟨((1033433283/8589934592), (-217615841/2147483648)), (129/4294967296), by norm_num⟩
  | 6 => ⟨((-133099423/2147483648), (896879737/17179869184)), (67/4294967296), by norm_num⟩
  | 7 => ⟨((940379353/34359738368), (-198020953/8589934592)), (239/34359738368), by norm_num⟩
  | 8 => ⟨((-363344063/34359738368), (153022793/17179869184)), (187/68719476736), by norm_num⟩
  | 9 => ⟨((499160855/137438953472), (-840888799/274877906944)), (259/274877906944), by norm_num⟩
  | 10 => ⟨((-308585479/274877906944), (519844595/549755813888)), (81/274877906944), by norm_num⟩
  | 11 => ⟨((173427421/549755813888), (-292156675/1099511627776)), (23/274877906944), by norm_num⟩
  | 12 => ⟨((-178690507/2199023255552), (301022895/4398046511104)), (191/8796093022208), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580452642685485/10141204801825835211973625643008), (3180436332289/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777790749968949/633825300114114700748351602688), (3759967352113/633825300114114700748351602688)), (92571/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888641440739745/39614081257132168796771975168), (4228961703455/39614081257132168796771975168)), (52083/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944173767852151/1237940039285380274899124224), (561503861619/309485009821345068724781056)), (6919/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((442503389400837/38685626227668133590597632), (4490635280415/154742504910672534362390528)), (110735/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774224812368211/4835703278458516698824704), (4208488186149/9671406556917033397649408)), (103847/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314455654253951/151115727451828646838272), (3680945278419/604462909807314587353088)), (90899/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235777716957809/9444732965739290427392), (747344827071/9444732965739290427392)), (147773/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324090331787499/1180591620717411303424), (1120409939125/1180591620717411303424)), (27721/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619827551801511/590295810358705651712), (3079154607899/295147905179352825856)), (152553/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455361989486549/18446744073709551616), (7691971862841/73786976294838206464)), (23853/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820375575823455/9223372036854775808), (4322670703229/4611686018427387904)), (214859/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99476401724331/72057594037927936), (8635191300961/1152921504606846976)), (107543/576460752303423488), by norm_num⟩
  | 5 => ⟨((74531931719633/9007199254740992), (7544385297401/144115188075855872)), (94229/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488528940783127/36028797018963968), (5646896598253/18014398509481984)), (283199/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485365724905981/9007199254740992), (1759679296641/1125899906842624)), (354899/9007199254740992), by norm_num⟩
  | 2 => ⟨((277518156699829/562949953421312), (14017855984195/2251799813685248)), (712503/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204352982591543/2251799813685248), (41756601313569/2251799813685248)), (537769/1125899906842624), by norm_num⟩
  | 0 => ⟨((1078525044871493/1125899906842624), (82330881797491/2251799813685248)), (1089169/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1078525044871493/1125899906842624), (82330881797491/2251799813685248)), (4154850010398482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2063276978409099/2251799813685248), (157733236223387/2251799813685248)), (2166325/1125899906842624), by norm_num⟩
  | 2 => ⟨((1879488616218107/2251799813685248), (144527658742923/1125899906842624)), (4273409/1125899906842624), by norm_num⟩
  | 3 => ⟨((1531630148011325/2251799813685248), (482526177833583/2251799813685248)), (8230817/1125899906842624), by norm_num⟩
  | 4 => ⟨((469193439212591/1125899906842624), (656409718735231/2251799813685248)), (29448715/2251799813685248), by norm_num⟩
  | 5 => ⟨((99852618340555/1125899906842624), (547087945552165/2251799813685248)), (41713043/2251799813685248), by norm_num⟩
  | 6 => ⟨((-921655777867977/18014398509481984), (194078224872167/4503599627370496)), (221341289/18014398509481984), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45376701/16777216), (-348468755/8388608)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5753657/2097152), (-1413920103/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-312953268346405/18014398509481984), (1116016404622617/18014398509481984)), (100835209/9007199254740992), by norm_num⟩
  | 1 => ⟨((233951369/4294967296), (-208572327/1073741824)), (19/536870912), by norm_num⟩
  | 2 => ⟨((-183388291/2147483648), (653977325/2147483648)), (15/268435456), by norm_num⟩
  | 3 => ⟨((191670975/2147483648), (-85439255/268435456)), (253/4294967296), by norm_num⟩
  | 4 => ⟨((-300491617/4294967296), (1071577159/4294967296)), (25/536870912), by norm_num⟩
  | 5 => ⟨((376875891/8589934592), (-1343969593/8589934592)), (253/8589934592), by norm_num⟩
  | 6 => ⟨((-24618587/1073741824), (351167407/4294967296)), (133/8589934592), by norm_num⟩
  | 7 => ⟨((352875141/34359738368), (-629190499/17179869184)), (15/2147483648), by norm_num⟩
  | 8 => ⟨((-276609491/68719476736), (986411585/68719476736)), (95/34359738368), by norm_num⟩
  | 9 => ⟨((192734991/137438953472), (-171827101/34359738368)), (267/274877906944), by norm_num⟩
  | 10 => ⟨((-60431945/137438953472), (431010305/274877906944)), (169/549755813888), by norm_num⟩
  | 11 => ⟨((275613111/2199023255552), (-982858413/2199023255552)), (97/1099511627776), by norm_num⟩
  | 12 => ⟨((-288061105/8796093022208), (256812239/2199023255552)), (51/2199023255552), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790200988601433/5070602400912917605986812821504), (2402269124671/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444433527790667/158456325028528675187087900672), (2839822000857/633825300114114700748351602688)), (1445/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1888577916096405/39614081257132168796771975168), (199627447255/2475880078570760549798248448)), (52029/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888280299306893/2475880078570760549798248448), (424089575949/309485009821345068724781056)), (110583/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221243326469191/19342813113834066795298816), (1695824150367/77371252455336267181195264)), (55303/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774193585733421/4835703278458516698824704), (3178535611121/9671406556917033397649408)), (51859/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628884139298527/302231454903657293676544), (2780084444717/604462909807314587353088)), (90779/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886134013013571/75557863725914323419136), (4515511537747/75557863725914323419136)), (73781/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324074009926605/1180591620717411303424), (846193661711/1180591620717411303424)), (13839/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809869300182873/295147905179352825856), (4651046067757/590295810358705651712)), (19037/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910668997478021/36893488147419103232), (5809282149781/73786976294838206464)), (95235/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910126775276763/4611686018427387904), (816153137221/1152921504606846976)), (13401/576460752303423488), by norm_num⟩
  | 6 => ⟨((1591502501580443/1152921504606846976), (6521461169749/1152921504606846976)), (53647/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192408327600565/144115188075855872), (1424388678637/36028797018963968)), (93979/72057594037927936), by norm_num⟩
  | 4 => ⟨((744189882908853/18014398509481984), (4264455476063/18014398509481984)), (282325/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485187436846657/9007199254740992), (2657677819509/2251799813685248)), (353587/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219813078060177/4503599627370496), (21170378140501/4503599627370496)), (709219/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203915227685617/2251799813685248), (15764393443481/1125899906842624)), (33405/70368744177664), by norm_num⟩
  | 0 => ⟨((2156413668973101/2251799813685248), (62155423519013/2251799813685248)), (539637/562949953421312), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2156413668973101/2251799813685248), (62155423519013/2251799813685248)), (2058551790477561773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((515838107235789/562949953421312), (119045044823817/2251799813685248)), (1063347/562949953421312), by norm_num⟩
  | 2 => ⟨((471095554047509/562949953421312), (109082468564945/1125899906842624)), (8244591/2251799813685248), by norm_num⟩
  | 3 => ⟨((777888952563451/1125899906842624), (365135590850747/2251799813685248)), (481133/70368744177664), by norm_num⟩
  | 4 => ⟨((507842854519131/1125899906842624), (126136853100489/562949953421312)), (3283471/281474976710656), by norm_num⟩
  | 5 => ⟨((86269809982725/562949953421312), (910314661533287/4503599627370496)), (17733873/1125899906842624), by norm_num⟩
  | 6 => ⟨((-312953268346405/18014398509481984), (1116016404622617/18014398509481984)), (100835209/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5753657/2097152), (-1413920103/33554432)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-93308067/33554432), (-358277985/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((164236547990161/9007199254740992), (1067293409220343/18014398509481984)), (40899857/4503599627370496), by norm_num⟩
  | 1 => ⟨((-124443195/2147483648), (-808695771/4294967296)), (125/4294967296), by norm_num⟩
  | 2 => ⟨((98871793/1073741824), (642519673/2147483648)), (201/4294967296), by norm_num⟩
  | 3 => ⟨((-418959841/4294967296), (-170163509/536870912)), (215/4294967296), by norm_num⟩
  | 4 => ⟨((20804327/268435456), (1081577583/4294967296)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((-423150535/8589934592), (-171865589/1073741824)), (55/2147483648), by norm_num⟩
  | 6 => ⟨((448265059/17179869184), (1456528249/17179869184)), (235/17179869184), by norm_num⟩
  | 7 => ⟨((-25439473/2147483648), (-1322550051/34359738368)), (215/34359738368), by norm_num⟩
  | 8 => ⟨((161696029/34359738368), (525391907/34359738368)), (173/68719476736), by norm_num⟩
  | 9 => ⟨((-456781053/274877906944), (-371049725/68719476736)), (247/274877906944), by norm_num⟩
  | 10 => ⟨((290334955/549755813888), (1842525/1073741824)), (159/549755813888), by norm_num⟩
  | 11 => ⟨((-335527315/2199023255552), (-545107189/1099511627776)), (185/2199023255552), by norm_num⟩
  | 12 => ⟨((355441289/8796093022208), (1154919993/8796093022208)), (99/4398046511104), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580353468412699/10141204801825835211973625643008), (1657225654043/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888839518064185/316912650057057350374175801344), (489738666687/158456325028528675187087900672)), (46197/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888516095695415/39614081257132168796771975168), (1101647778157/19807040628566084398385987584)), (103955/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944107400273621/1237940039285380274899124224), (585084414735/618970019642690137449562112)), (110467/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769881321355457/154742504910672534362390528), (2339591170717/154742504910672534362390528)), (110483/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548326182928309/9671406556917033397649408), (548143473137/2417851639229258349412352)), (103595/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257715134639013/604462909807314587353088), (479427419759/151115727451828646838272)), (90663/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886048068064233/75557863725914323419136), (194674567753/4722366482869645213696)), (147359/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648115971406101/2361183241434822606848), (1167398030587/2361183241434822606848)), (27637/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619651054309169/590295810358705651712), (3208235516741/590295810358705651712)), (152049/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910614720889799/36893488147419103232), (500891656355/9223372036854775808)), (95065/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455033158795363/2305843009213693952), (2251841160211/4611686018427387904)), (26749/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1591383091578833/1152921504606846976), (2249130031437/576460752303423488)), (107055/576460752303423488), by norm_num⟩
  | 5 => ⟨((298076383208813/36028797018963968), (1964942861483/72057594037927936)), (187481/144115188075855872), by norm_num⟩
  | 4 => ⟨((372057235068949/9007199254740992), (2941332706013/18014398509481984)), (140745/18014398509481984), by norm_num⟩
  | 3 => ⟨((742502385484695/4503599627370496), (7332092243885/9007199254740992)), (88083/2251799813685248), by norm_num⟩
  | 2 => ⟨((554866310682509/1125899906842624), (7300324834419/2251799813685248)), (706081/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203436861129023/2251799813685248), (21742778864479/2251799813685248)), (265669/562949953421312), by norm_num⟩
  | 0 => ⟨((2155628365195229/2251799813685248), (42856610077823/2251799813685248)), (2139659/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2155628365195229/2251799813685248), (42856610077823/2251799813685248)), (8162151345259856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062748620715601/2251799813685248), (2564141241553/70368744177664)), (261125/140737488355328), by norm_num⟩
  | 2 => ⟨((943289725501311/1125899906842624), (150327503244325/2251799813685248)), (7958949/2251799813685248), by norm_num⟩
  | 3 => ⟨((392639661529879/562949953421312), (1967903468939/17592186044416)), (14398829/2251799813685248), by norm_num⟩
  | 4 => ⟨((1067237436456895/2251799813685248), (87843199249583/562949953421312)), (2913353/281474976710656), by norm_num⟩
  | 5 => ⟨((56373400575663/281474976710656), (166532655713953/1125899906842624)), (58732219/4503599627370496), by norm_num⟩
  | 6 => ⟨((164236547990161/9007199254740992), (1067293409220343/18014398509481984)), (40899857/4503599627370496), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-93308067/33554432), (-358277985/8388608)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-47253303/16777216), (-1451520215/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((807499996459457/18014398509481984), (713425991559039/18014398509481984)), (59719225/9007199254740992), by norm_num⟩
  | 1 => ⟨((-154926909/1073741824), (-547511501/4294967296)), (93/4294967296), by norm_num⟩
  | 2 => ⟨((249345241/1073741824), (881185767/4294967296)), (19/536870912), by norm_num⟩
  | 3 => ⟨((-1070148491/4294967296), (-472737927/2147483648)), (165/4294967296), by norm_num⟩
  | 4 => ⟨((861168777/4294967296), (380421171/2147483648)), (135/4294967296), by norm_num⟩
  | 5 => ⟨((-1108798143/8589934592), (-979622809/8589934592)), (11/536870912), by norm_num⟩
  | 6 => ⟨((74355907/1073741824), (525547363/8589934592)), (3/268435456), by norm_num⟩
  | 7 => ⟨((-547068415/17179869184), (-120833693/4294967296)), (179/34359738368), by norm_num⟩
  | 8 => ⟨((110059081/8589934592), (777897307/68719476736)), (73/34359738368), by norm_num⟩
  | 9 => ⟨((-314903569/68719476736), (-69554301/17179869184)), (53/68719476736), by norm_num⟩
  | 10 => ⟨((202727097/137438953472), (358218653/274877906944)), (139/549755813888), by norm_num⟩
  | 11 => ⟨((-7415379/17179869184), (-419295041/1099511627776)), (165/2199023255552), by norm_num⟩
  | 12 => ⟨((509209263/4398046511104), (899772447/8796093022208)), (179/8796093022208), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580306940107137/10141204801825835211973625643008), (942600728129/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444406357738879/158456325028528675187087900672), (1114153110059/633825300114114700748351602688)), (92311/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472113970126231/9903520314283042199192993792), (1253119092791/39614081257132168796771975168)), (103857/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472037735670375/618970019642690137449562112), (1331056734997/2475880078570760549798248448)), (110355/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769817599206179/154742504910672534362390528), (1330626878655/154742504910672534362390528)), (110365/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24191665429679/151115727451828646838272), (1247006168571/9671406556917033397649408)), (103477/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314415783149495/151115727451828646838272), (1090674083671/604462909807314587353088)), (90553/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471490958600419/18889465931478580854784), (1771490257005/75557863725914323419136)), (147165/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296169003243473/4722366482869645213696), (1327869914097/4722366482869645213696)), (55195/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50611402964845/18446744073709551616), (1824606851933/590295810358705651712)), (151813/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821122315314939/73786976294838206464), (284867331179/9223372036854775808)), (189805/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910006452058493/4611686018427387904), (2561306039281/9223372036854775808)), (213585/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591264341132681/1152921504606846976), (159886548273/72057594037927936)), (106827/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192202726450555/144115188075855872), (139681579769/9007199254740992)), (11689/9007199254740992), by norm_num⟩
  | 4 => ⟨((744038461938217/18014398509481984), (3345357660647/36028797018963968)), (280689/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484818572074527/9007199254740992), (4169474805777/9007199254740992)), (351131/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109552122073671/2251799813685248), (4151197617665/2251799813685248)), (175769/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202923632640775/2251799813685248), (12362599251693/2251799813685248)), (132083/281474976710656), by norm_num⟩
  | 0 => ⟨((2154713621856261/2251799813685248), (12181784363101/1125899906842624)), (530399/562949953421312), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154713621856261/2251799813685248), (12181784363101/1125899906842624)), (2023311617137718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2061549690393893/2251799813685248), (46626270321485/2251799813685248)), (2053079/1125899906842624), by norm_num⟩
  | 2 => ⟨((1886407970665555/2251799813685248), (42686908739089/1125899906842624)), (7688521/2251799813685248), by norm_num⟩
  | 3 => ⟨((788535091240603/1125899906842624), (71520500533931/1125899906842624)), (6732431/1125899906842624), by norm_num⟩
  | 4 => ⟨((1069756103355/2199023255552), (25045043556425/281474976710656)), (20571155/2251799813685248), by norm_num⟩
  | 5 => ⟨((128766238008187/562949953421312), (389876196325021/4503599627370496)), (5918801/562949953421312), by norm_num⟩
  | 6 => ⟨((807499996459457/18014398509481984), (713425991559039/18014398509481984)), (59719225/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/16777216), (-1451520215/33554432)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-95658131/33554432), (-183650801/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((510559171218195/9007199254740992), (203309013812683/18014398509481984)), (39021805/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1586390561/8589934592), (-157928561/4294967296)), (31/2147483648), by norm_num⟩
  | 2 => ⟨((1292153399/4294967296), (257273249/4294967296)), (103/4294967296), by norm_num⟩
  | 3 => ⟨((-350830043/1073741824), (-279407027/4294967296)), (57/2147483648), by norm_num⟩
  | 4 => ⟨((1143038149/4294967296), (227583767/4294967296)), (95/4294967296), by norm_num⟩
  | 5 => ⟨((-1489651455/8589934592), (-296595953/8589934592)), (63/4294967296), by norm_num⟩
  | 6 => ⟨((202226177/2147483648), (322112749/17179869184)), (139/17179869184), by norm_num⟩
  | 7 => ⟨((-752997037/17179869184), (-149924919/17179869184)), (131/34359738368), by norm_num⟩
  | 8 => ⟨((153333565/8589934592), (122117465/34359738368)), (27/17179869184), by norm_num⟩
  | 9 => ⟨((-222033581/34359738368), (-176831329/137438953472)), (159/274877906944), by norm_num⟩
  | 10 => ⟨((1157450947/549755813888), (28806677/68719476736)), (53/274877906944), by norm_num⟩
  | 11 => ⟨((-85706521/137438953472), (-273032537/2199023255552)), (127/2199023255552), by norm_num⟩
  | 12 => ⟨((1489280637/8796093022208), (296522121/8796093022208)), (35/2199023255552), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580262236925127/10141204801825835211973625643008), (256007640927/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444393302576117/158456325028528675187087900672), (151291806913/316912650057057350374175801344)), (46115/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888397180183137/39614081257132168796771975168), (340323417647/39614081257132168796771975168)), (103761/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944044318504957/1237940039285380274899124224), (361488556331/2475880078570760549798248448)), (110249/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884877682402553/77371252455336267181195264), (180685207087/77371252455336267181195264)), (27563/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548208318417505/9671406556917033397649408), (169329645903/4835703278458516698824704)), (103363/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314403055689349/151115727451828646838272), (296201470271/604462909807314587353088)), (45223/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885881247538579/75557863725914323419136), (15034136743/2361183241434822606848)), (146979/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296107186887017/4722366482869645213696), (360613775455/4722366482869645213696)), (110239/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50608753071719/18446744073709551616), (495510237635/590295810358705651712)), (75793/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821016620517945/73786976294838206464), (618887668691/73786976294838206464)), (189493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819894410537107/9223372036854775808), (173890411027/2305843009213693952)), (213195/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591146362823923/1152921504606846976), (43418997121/72057594037927936)), (106607/576460752303423488), by norm_num⟩
  | 5 => ⟨((74506254603279/9007199254740992), (606902484671/144115188075855872)), (186585/144115188075855872), by norm_num⟩
  | 4 => ⟨((371981024371689/9007199254740992), (908430337263/36028797018963968)), (17495/2251799813685248), by norm_num⟩
  | 3 => ⟨((1484629548340353/9007199254740992), (566089992221/4503599627370496)), (349979/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218732191909003/4503599627370496), (1127159029215/2251799813685248)), (700195/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202380429008989/2251799813685248), (839120902899/562949953421312)), (1050899/2251799813685248), by norm_num⟩
  | 0 => ⟨((2153686037395219/2251799813685248), (1653414575517/562949953421312)), (526073/562949953421312), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153686037395219/2251799813685248), (1653414575517/562949953421312)), (2006809236766624273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2059827778209115/2251799813685248), (1581373203637/281474976710656)), (4037573/2251799813685248), by norm_num⟩
  | 2 => ⟨((1884150803574741/2251799813685248), (2893113706441/281474976710656)), (3716043/1125899906842624), by norm_num⟩
  | 3 => ⟨((197036196456977/281474976710656), (38732128720823/2251799813685248)), (12590095/2251799813685248), by norm_num⟩
  | 4 => ⟨((1102757279232427/2251799813685248), (847281281117/35184372088832)), (18059579/2251799813685248), by norm_num⟩
  | 5 => ⟨((1077478690810207/4503599627370496), (26555699159563/1125899906842624)), (18558161/2251799813685248), by norm_num⟩
  | 6 => ⟨((510559171218195/9007199254740992), (203309013812683/18014398509481984)), (39021805/9007199254740992), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95658131/33554432), (-183650801/4194304)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6047887/2097152), (-1486225035/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((959121398503369/18014398509481984), (-153965798995197/9007199254740992)), (83215431/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1507333595/8589934592), (241969183/4294967296)), (133/8589934592), by norm_num⟩
  | 2 => ⟨((38811919/134217728), (-398745477/4294967296)), (111/4294967296), by norm_num⟩
  | 3 => ⟨((-1364456037/4294967296), (438066681/4294967296)), (31/1073741824), by norm_num⟩
  | 4 => ⟨((1124256127/4294967296), (-360949079/4294967296)), (13/536870912), by norm_num⟩
  | 5 => ⟨((-370536479/2147483648), (475851713/8589934592)), (139/8589934592), by norm_num⟩
  | 6 => ⟨((407075929/4294967296), (-130694135/4294967296)), (39/4294967296), by norm_num⟩
  | 7 => ⟨((-95832561/2147483648), (492281769/34359738368)), (149/34359738368), by norm_num⟩
  | 8 => ⟨((631696975/34359738368), (-405620101/68719476736)), (125/68719476736), by norm_num⟩
  | 9 => ⟨((-925320079/137438953472), (297079485/137438953472)), (93/137438953472), by norm_num⟩
  | 10 => ⟨((304970403/137438953472), (-12239069/17179869184)), (125/549755813888), by norm_num⟩
  | 11 => ⟨((-365502799/549755813888), (469387343/2199023255552)), (19/274877906944), by norm_num⟩
  | 12 => ⟨((803091733/4398046511104), (-515674703/8796093022208)), (169/8796093022208), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395054805263161/2535301200456458802993406410752), (-12645936411/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777522296223509/633825300114114700748351602688), (-478266266405/633825300114114700748351602688)), (11531/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944169955955653/19807040628566084398385987584), (-268958341941/19807040628566084398385987584)), (51891/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888027801837595/2475880078570760549798248448), (-71421058969/309485009821345068724781056)), (1723/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1769694543541881/154742504910672534362390528), (-285589787415/77371252455336267181195264)), (27569/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774075656629037/4835703278458516698824704), (-535280236469/9671406556917033397649408)), (25847/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257562358013725/604462909807314587353088), (-468169691095/604462909807314587353088)), (90469/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471450061254225/18889465931478580854784), (-47524999461/4722366482869645213696)), (147019/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296046459213173/4722366482869645213696), (-569971416825/4722366482869645213696)), (1723/73786976294838206464), by norm_num⟩
  | 9 => ⟨((809698318540397/295147905179352825856), (-391588577563/295147905179352825856)), (151635/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910456176489101/36893488147419103232), (-978171818553/73786976294838206464)), (189561/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819777190604259/9223372036854775808), (-1099344929793/9223372036854775808)), (6665/288230376151711744), by norm_num⟩
  | 6 => ⟨((6214957984901/4503599627370496), (-548986824225/576460752303423488)), (106655/576460752303423488), by norm_num⟩
  | 5 => ⟨((1191997708604741/144115188075855872), (-959186552621/144115188075855872)), (23335/18014398509481984), by norm_num⟩
  | 4 => ⟨((371942694322975/9007199254740992), (-1435704794391/36028797018963968)), (280087/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484438295479639/9007199254740992), (-1789262583185/9007199254740992)), (350229/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218350876231397/4503599627370496), (-3562471411655/4503599627370496)), (700821/4503599627370496), by norm_num⟩
  | 1 => ⟨((2201811423239711/2251799813685248), (-2651876159069/1125899906842624)), (1052151/2251799813685248), by norm_num⟩
  | 0 => ⟨((2152559852704429/2251799813685248), (-10448758385813/2251799813685248)), (1054027/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2152559852704429/2251799813685248), (-10448758385813/2251799813685248)), (4020793919089889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((8037675981251/8796093022208), (-2497066754693/281474976710656)), (4049863/2251799813685248), by norm_num⟩
  | 2 => ⟨((117503343022761/140737488355328), (-9127058309685/562949953421312)), (934151/281474976710656), by norm_num⟩
  | 3 => ⟨((784543156665783/1125899906842624), (-60962285223903/2251799813685248)), (3180315/562949953421312), by norm_num⟩
  | 4 => ⟨((545855684755897/1125899906842624), (-84958784340331/2251799813685248)), (9208755/1125899906842624), by norm_num⟩
  | 5 => ⟨((1052150117506239/4503599627370496), (-164757933170705/4503599627370496)), (4812003/562949953421312), by norm_num⟩
  | 6 => ⟨((959121398503369/18014398509481984), (-153965798995197/9007199254740992)), (83215431/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-6047887/2097152), (-1486225035/33554432)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 12 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile036Terms3
