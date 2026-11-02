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
namespace Reinmann.XiRectangle.Tile042Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨42,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (3525/256))
  have he : value ((7/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-45376701/16777216), (-357037659/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((180918073524077/18014398509481984), (1191377245654103/18014398509481984)), (46612269/4503599627370496), by norm_num⟩
  | 1 => ⟨((-16666217/536870912), (-438999849/2147483648)), (277/8589934592), by norm_num⟩
  | 2 => ⟨((206063937/4294967296), (678483585/2147483648)), (27/536870912), by norm_num⟩
  | 3 => ⟨((-212317459/4294967296), (-699073855/2147483648)), (7/134217728), by norm_num⟩
  | 4 => ⟨((82035285/2147483648), (540216741/2147483648)), (175/4294967296), by norm_num⟩
  | 5 => ⟨((-202859639/8589934592), (-20872911/134217728)), (109/4294967296), by norm_num⟩
  | 6 => ⟨((209015919/17179869184), (688203243/8589934592)), (113/8589934592), by norm_num⟩
  | 7 => ⟨((-184593451/34359738368), (-303895063/8589934592)), (201/34359738368), by norm_num⟩
  | 8 => ⟨((35661637/17179869184), (939352541/68719476736)), (157/68719476736), by norm_num⟩
  | 9 => ⟨((-195967349/274877906944), (-645239685/137438953472)), (217/274877906944), by norm_num⟩
  | 10 => ⟨((121148679/549755813888), (1595570607/1099511627776)), (135/549755813888), by norm_num⟩
  | 11 => ⟨((-272345971/4398046511104), (-896722997/2199023255552)), (305/4398046511104), by norm_num⟩
  | 12 => ⟨((140305493/8796093022208), (230984071/2199023255552)), (317/17592186044416), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580452642685485/10141204801825835211973625643008), (1849827704123/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777795767917475/633825300114114700748351602688), (1093449301897/316912650057057350374175801344)), (361/2475880078570760549798248448), by norm_num⟩
  | 16 => ⟨((472161839948081/9903520314283042199192993792), (614921337345/9903520314283042199192993792)), (51991/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888354192325235/2475880078570760549798248448), (2612694729223/2475880078570760549798248448)), (110497/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885010313666559/77371252455336267181195264), (652971005719/38685626227668133590597632)), (110515/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548456691171711/9671406556917033397649408), (2447780219635/9671406556917033397649408)), (103627/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628914619150043/302231454903657293676544), (2140947004567/604462909807314587353088)), (90693/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886233315915927/75557863725914323419136), (3477425866727/75557863725914323419136)), (36853/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((648185364776401/2361183241434822606848), (1303329392255/2361183241434822606848)), (110591/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619841643945317/590295810358705651712), (3581865027383/590295810358705651712)), (152113/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455366829008739/18446744073709551616), (2236948808125/36893488147419103232)), (95109/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820399745545749/9223372036854775808), (5028417639501/9223372036854775808)), (214101/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591649580220257/1152921504606846976), (5022527332725/1152921504606846976)), (107117/576460752303423488), by norm_num⟩
  | 5 => ⟨((298134503080547/36028797018963968), (4388093291557/144115188075855872)), (46901/36028797018963968), by norm_num⟩
  | 4 => ⟨((744288133380793/18014398509481984), (6568924838557/36028797018963968)), (281705/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485436499416635/9007199254740992), (1023509642789/1125899906842624)), (352655/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110160720568669/2251799813685248), (4076776819611/1125899906842624)), (88361/562949953421312), by norm_num⟩
  | 1 => ⟨((2204703118889613/2251799813685248), (24288705790837/2251799813685248)), (1064291/2251799813685248), by norm_num⟩
  | 0 => ⟨((1079044678335355/1125899906842624), (47893552618063/2251799813685248)), (268063/281474976710656), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079044678335355/1125899906842624), (47893552618063/2251799813685248)), (1022579194188976199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2067260087109899/2251799813685248), (22950211988213/562949953421312)), (4201741/2251799813685248), by norm_num⟩
  | 2 => ⟨((947050631710581/1125899906842624), (84277575556413/1125899906842624)), (8057391/2251799813685248), by norm_num⟩
  | 3 => ⟨((790303102321971/1125899906842624), (283560308281981/2251799813685248)), (14761197/2251799813685248), by norm_num⟩
  | 4 => ⟨((1073767530768579/2251799813685248), (99519766352529/562949953421312)), (24440299/2251799813685248), by norm_num⟩
  | 5 => ⟨((441651056977159/2251799813685248), (379646869600311/2251799813685248)), (63899769/4503599627370496), by norm_num⟩
  | 6 => ⟨((180918073524077/18014398509481984), (1191377245654103/18014398509481984)), (46612269/4503599627370496), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45376701/16777216), (-357037659/8388608)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-5753657/2097152), (-724344315/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((100105176651189/2251799813685248), (837905361269467/18014398509481984)), (16877431/2251799813685248), by norm_num⟩
  | 1 => ⟨((-598677067/4294967296), (-626384595/4294967296)), (103/4294967296), by norm_num⟩
  | 2 => ⟨((29330445/134217728), (982012637/4294967296)), (163/4294967296), by norm_num⟩
  | 3 => ⟨((-245241175/1073741824), (-1026364981/4294967296)), (43/1073741824), by norm_num⟩
  | 4 => ⟨((384476143/2147483648), (804540365/4294967296)), (137/4294967296), by norm_num⟩
  | 5 => ⟨((-482209089/4294967296), (-126131583/1073741824)), (87/4294967296), by norm_num⟩
  | 6 => ⟨((1007975873/17179869184), (131828283/2147483648)), (23/2147483648), by norm_num⟩
  | 7 => ⟨((-56437545/2147483648), (-944792729/34359738368)), (167/34359738368), by norm_num⟩
  | 8 => ⟨((44239899/4294967296), (370299017/34359738368)), (133/68719476736), by norm_num⟩
  | 9 => ⟨((-986410293/274877906944), (-1032062601/274877906944)), (47/68719476736), by norm_num⟩
  | 10 => ⟨((309288377/274877906944), (647205263/549755813888)), (15/68719476736), by norm_num⟩
  | 11 => ⟨((-705288667/2199023255552), (-92241289/274877906944)), (69/1099511627776), by norm_num⟩
  | 12 => ⟨((737142845/8796093022208), (385629371/4398046511104)), (73/4398046511104), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790200988601433/5070602400912917605986812821504), (1052525271349/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777737607059841/633825300114114700748351602688), (1244233791851/633825300114114700748351602688)), (92323/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888582039375095/39614081257132168796771975168), (1399432528869/39614081257132168796771975168)), (1623/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1888284936376273/2475880078570760549798248448), (371620286997/618970019642690137449562112)), (110373/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769951536570897/154742504910672534362390528), (743006743161/77371252455336267181195264)), (110383/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548392093958291/9671406556917033397649408), (1392640955195/9671406556917033397649408)), (103495/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314443222740689/151115727451828646838272), (1218064375247/604462909807314587353088)), (90569/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886142079716319/75557863725914323419136), (989212114907/37778931862957161709568)), (147195/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296302589276759/4722366482869645213696), (1483004573177/4722366482869645213696)), (55207/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202468552079049/73786976294838206464), (2037810094993/590295810358705651712)), (151849/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455337869797387/18446744073709551616), (2545282412543/73786976294838206464)), (189855/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910135193082707/4611686018427387904), (178795156343/576460752303423488)), (213647/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795760707307907/576460752303423488), (2857326088075/1152921504606846976)), (53431/288230376151711744), by norm_num⟩
  | 5 => ⟨((596213603449431/72057594037927936), (2496344652517/144115188075855872)), (93547/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488412728812943/36028797018963968), (3736898836675/36028797018963968)), (70203/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485236730114527/9007199254740992), (4657821459743/9007199254740992)), (351315/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219935783418153/4503599627370496), (9275855046143/4503599627370496)), (703535/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204159060855357/2251799813685248), (13814726041751/2251799813685248)), (1057579/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157137321846427/2251799813685248), (27235695402995/2251799813685248)), (1062169/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157137321846427/2251799813685248), (27235695402995/2251799813685248)), (4051853184226607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((516531222482929/562949953421312), (52181490275631/2251799813685248)), (4121457/2251799813685248), by norm_num⟩
  | 2 => ⟨((947275403199823/1125899906842624), (47878801302397/1125899906842624)), (7754251/2251799813685248), by norm_num⟩
  | 3 => ⟨((1589907423304085/2251799813685248), (80565617836563/1125899906842624)), (6853785/1125899906842624), by norm_num⟩
  | 4 => ⟨((1111041187748135/2251799813685248), (56884219051337/562949953421312)), (10659245/1125899906842624), by norm_num⟩
  | 5 => ⟨((1050394874048787/4503599627370496), (112267013994445/1125899906842624)), (50690943/4503599627370496), by norm_num⟩
  | 6 => ⟨((100105176651189/2251799813685248), (837905361269467/18014398509481984)), (16877431/2251799813685248), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5753657/2097152), (-724344315/16777216)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-93308067/33554432), (-1468352397/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1089294668158693/18014398509481984), (61464889402991/4503599627370496)), (85488145/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1650732561/8589934592), (-186289527/4294967296)), (33/2147483648), by norm_num⟩
  | 2 => ⟨((655764617/2147483648), (2312649/33554432)), (107/4294967296), by norm_num⟩
  | 3 => ⟨((-173671271/536870912), (-156794091/2147483648)), (115/4294967296), by norm_num⟩
  | 4 => ⟨((68992081/268435456), (249150031/4294967296)), (93/4294967296), by norm_num⟩
  | 5 => ⟨((-701633751/4294967296), (-79181221/2147483648)), (15/1073741824), by norm_num⟩
  | 6 => ⟨((371638305/4294967296), (167761455/8589934592)), (129/17179869184), by norm_num⟩
  | 7 => ⟨((-1349813187/34359738368), (-304659963/34359738368)), (119/34359738368), by norm_num⟩
  | 8 => ⟨((536222371/34359738368), (242056441/68719476736)), (3/2147483648), by norm_num⟩
  | 9 => ⟨((-1514794275/274877906944), (-170948533/137438953472)), (69/137438953472), by norm_num⟩
  | 10 => ⟨((962819549/549755813888), (13582091/34359738368)), (89/549755813888), by norm_num⟩
  | 11 => ⟨((-1112688129/2199023255552), (-125569793/1099511627776)), (13/274877906944), by norm_num⟩
  | 12 => ⟨((589363795/4398046511104), (266045041/8796093022208)), (7/549755813888), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580353468412699/10141204801825835211973625643008), (289161075869/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777681032405441/633825300114114700748351602688), (170904136571/316912650057057350374175801344)), (46117/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944259225005517/19807040628566084398385987584), (24027658407/2475880078570760549798248448)), (51883/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888217448221005/2475880078570760549798248448), (408354406995/2475880078570760549798248448)), (55127/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769884133312069/154742504910672534362390528), (408224219359/154742504910672534362390528)), (110257/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548328993539565/9671406556917033397649408), (95642984977/2417851639229258349412352)), (103369/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257717768158405/604462909807314587353088), (83653061917/151115727451828646838272)), (90451/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235756584233451/9444732965739290427392), (543485918077/75557863725914323419136)), (36747/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296235682352221/4722366482869645213696), (101846991821/1180591620717411303424)), (55123/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809828329470643/295147905179352825856), (559790701621/590295810358705651712)), (151597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910618570277071/36893488147419103232), (699187205803/73786976294838206464)), (47377/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820142247269925/9223372036854775808), (392914245525/4611686018427387904)), (106607/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591393889551099/1152921504606846976), (196220803223/288230376151711744)), (53309/288230376151711744), by norm_num⟩
  | 5 => ⟨((149039538912893/18014398509481984), (342855453055/72057594037927936)), (93303/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488247758791339/36028797018963968), (256611593675/9007199254740992)), (279957/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485032911339739/9007199254740992), (1279356587267/9007199254740992)), (350033/9007199254740992), by norm_num⟩
  | 2 => ⟨((277441911082441/562949953421312), (1273821657811/2251799813685248)), (350165/2251799813685248), by norm_num⟩
  | 1 => ⟨((2203576041644673/2251799813685248), (948477487911/562949953421312)), (1051169/2251799813685248), by norm_num⟩
  | 0 => ⟨((2156041375454583/2251799813685248), (934789327285/281474976710656)), (1052547/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2156041375454583/2251799813685248), (934789327285/281474976710656)), (4015148167136764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2064330256726947/2251799813685248), (7160297126631/1125899906842624)), (1011283/562949953421312), by norm_num⟩
  | 2 => ⟨((946188534060827/1125899906842624), (26256717699019/2251799813685248)), (7468175/2251799813685248), by norm_num⟩
  | 3 => ⟨((397504424124271/562949953421312), (44131463335055/2251799813685248)), (12726437/2251799813685248), by norm_num⟩
  | 4 => ⟨((560931010333343/1125899906842624), (62323308891487/2251799813685248)), (4617839/562949953421312), by norm_num⟩
  | 5 => ⟨((139298594723853/562949953421312), (31049897429919/1125899906842624)), (19427579/2251799813685248), by norm_num⟩
  | 6 => ⟨((1089294668158693/18014398509481984), (61464889402991/4503599627370496)), (85488145/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-93308067/33554432), (-1468352397/33554432)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-47253303/16777216), (-1487213335/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1015788792577963/18014398509481984), (-359452387093323/18014398509481984)), (91059327/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1559113497/8589934592), (551716137/8589934592)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((627324093/2147483648), (-221988217/2147483648)), (29/1073741824), by norm_num⟩
  | 3 => ⟨((-336546393/1073741824), (476368337/4294967296)), (63/2147483648), by norm_num⟩
  | 4 => ⟨((1083301049/4294967296), (-383342631/4294967296)), (103/4294967296), by norm_num⟩
  | 5 => ⟨((-1394804623/8589934592), (493572931/8589934592)), (135/8589934592), by norm_num⟩
  | 6 => ⟨((1496567627/17179869184), (-529583325/17179869184)), (147/17179869184), by norm_num⟩
  | 7 => ⟨((-688180765/17179869184), (487046561/34359738368)), (137/34359738368), by norm_num⟩
  | 8 => ⟨((553792107/34359738368), (-24495975/4294967296)), (7/4294967296), by norm_num⟩
  | 9 => ⟨((-1584522689/274877906944), (35044223/17179869184)), (81/137438953472), by norm_num⟩
  | 10 => ⟨((255019089/137438953472), (-360969607/549755813888)), (53/274877906944), by norm_num⟩
  | 11 => ⟨((-1193999681/2199023255552), (422515033/2199023255552)), (63/1099511627776), by norm_num⟩
  | 12 => ⟨((320278059/2199023255552), (-226670571/4398046511104)), (137/8796093022208), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580306940107137/10141204801825835211973625643008), (-13844894173/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777625949905971/633825300114114700748351602688), (-523668830407/633825300114114700748351602688)), (23063/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((118028530779779/2475880078570760549798248448), (-147246279663/9903520314283042199192993792)), (103787/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888151630905089/2475880078570760549798248448), (-625617020915/2475880078570760549798248448)), (55139/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884909165064365/77371252455336267181195264), (-625415007169/154742504910672534362390528)), (55141/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193533414758487/1208925819614629174706176), (-586112021495/9671406556917033397649408)), (51697/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157207977141233/75557863725914323419136), (-512633574511/604462909807314587353088)), (90475/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942982515790447/37778931862957161709568), (-832627695187/75557863725914323419136)), (73515/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296169975247491/4722366482869645213696), (-312059680221/2361183241434822606848)), (13785/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619566351649915/590295810358705651712), (-857593489121/590295810358705651712)), (4739/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1821124316381677/73786976294838206464), (-66946039585/4611686018427387904)), (94789/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820015402455665/9223372036854775808), (-601926970767/4611686018427387904)), (213301/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795633573825665/576460752303423488), (-1202387227179/1152921504606846976)), (106667/576460752303423488), by norm_num⟩
  | 5 => ⟨((74512845489803/9007199254740992), (-525220586187/72057594037927936)), (11669/9007199254740992), by norm_num⟩
  | 4 => ⟨((1488081814776881/36028797018963968), (-1572372451853/36028797018963968)), (140065/18014398509481984), by norm_num⟩
  | 3 => ⟨((742412942714775/4503599627370496), (-1959722743251/9007199254740992)), (350293/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219122447299211/4503599627370496), (-975567688099/1125899906842624)), (350489/2251799813685248), by norm_num⟩
  | 1 => ⟨((275369974903853/281474976710656), (-5810656766385/2251799813685248)), (1052465/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154820929985017/2251799813685248), (-5725718132053/1125899906842624)), (2108989/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154820929985017/2251799813685248), (-5725718132053/1125899906842624)), (8045154580123137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1030980213403195/1125899906842624), (-21916508199635/2251799813685248)), (4057773/2251799813685248), by norm_num⟩
  | 2 => ⟨((943956128459417/1125899906842624), (-40137646629845/2251799813685248)), (7510349/2251799813685248), by norm_num⟩
  | 3 => ⟨((1582112955821283/2251799813685248), (-67302923266831/2251799813685248)), (3215279/562949953421312), by norm_num⟩
  | 4 => ⟨((34674370617789/70368744177664), (-47286986266703/1125899906842624)), (9420611/1125899906842624), by norm_num⟩
  | 5 => ⟨((135694036998401/562949953421312), (-1456298625877/35184372088832)), (40301505/4503599627370496), by norm_num⟩
  | 6 => ⟨((1015788792577963/18014398509481984), (-359452387093323/18014398509481984)), (91059327/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/16777216), (-1487213335/33554432)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-95658131/33554432), (-752667217/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((663244849439763/18014398509481984), (-100321630740923/2251799813685248)), (63294161/9007199254740992), by norm_num⟩
  | 1 => ⟨((-257601231/2147483648), (155857829/1073741824)), (25/1073741824), by norm_num⟩
  | 2 => ⟨((839289679/4294967296), (-507799853/2147483648)), (165/4294967296), by norm_num⟩
  | 3 => ⟨((-911495599/4294967296), (551486981/2147483648)), (181/4294967296), by norm_num⟩
  | 4 => ⟨((185608791/1073741824), (-14037483/67108864)), (149/4294967296), by norm_num⟩
  | 5 => ⟨((-967570175/8589934592), (585414077/4294967296)), (49/2147483648), by norm_num⟩
  | 6 => ⟨((525406173/8589934592), (-317889263/4294967296)), (27/2147483648), by norm_num⟩
  | 7 => ⟨((-489092581/17179869184), (591836519/17179869184)), (51/8589934592), by norm_num⟩
  | 8 => ⟨((796755423/68719476736), (-964130257/68719476736)), (21/8589934592), by norm_num⟩
  | 9 => ⟨((-576868019/137438953472), (349025495/68719476736)), (123/137438953472), by norm_num⟩
  | 10 => ⟨((375898339/274877906944), (-454863503/274877906944)), (81/274877906944), by norm_num⟩
  | 11 => ⟨((-222675105/549755813888), (1077810331/2199023255552)), (97/1099511627776), by norm_num⟩
  | 12 => ⟨((483664659/4398046511104), (-1170536703/8796093022208)), (213/8796093022208), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580262236925127/10141204801825835211973625643008), (-1146513122353/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888786136985031/316912650057057350374175801344), (-677550253197/316912650057057350374175801344)), (46167/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888396076106347/39614081257132168796771975168), (-95257180783/2475880078570760549798248448)), (103885/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888087395369477/2475880078570760549798248448), (-404725352667/618970019642690137449562112)), (27597/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442438511534349/38685626227668133590597632), (-404593050265/38685626227668133590597632)), (110399/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193525875049555/1208925819614629174706176), (-758330945213/4835703278458516698824704)), (103511/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257610987799315/604462909807314587353088), (-1326517372977/604462909807314587353088)), (11323/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((235734885966799/9444732965739290427392), (-1077268979169/37778931862957161709568)), (147221/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296105433331853/4722366482869645213696), (-100936428697/295147905179352825856)), (27609/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619477470210429/590295810358705651712), (-1109553251141/295147905179352825856)), (151881/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910506505275705/36893488147419103232), (-1385821295259/36893488147419103232)), (94949/36893488147419103232), by norm_num⟩
  | 7 => ⟨((454972475886861/2305843009213693952), (-3115020189139/9223372036854775808)), (213701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795570649984893/576460752303423488), (-3111177548291/1152921504606846976)), (26723/144115188075855872), by norm_num⟩
  | 5 => ⟨((298023755042487/36028797018963968), (-84936362031/4503599627370496)), (93577/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487915274937535/36028797018963968), (-2034163658757/18014398509481984)), (140459/18014398509481984), by norm_num⟩
  | 3 => ⟨((742308178252337/4503599627370496), (-2535181153299/4503599627370496)), (351475/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218699358819475/4503599627370496), (-10095722829885/4503599627370496)), (703935/4503599627370496), by norm_num⟩
  | 1 => ⟨((550578800124745/562949953421312), (-234868186351/35184372088832)), (66149/140737488355328), by norm_num⟩
  | 0 => ⟨((2153492527449831/2251799813685248), (-29617939918201/2251799813685248)), (2126767/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153492527449831/2251799813685248), (-29617939918201/2251799813685248)), (8112972268111418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1029543748791109/1125899906842624), (-221288308137/8796093022208)), (4123785/2251799813685248), by norm_num⟩
  | 2 => ⟨((470360652879921/562949953421312), (-103603267381463/2251799813685248)), (1937305/562949953421312), by norm_num⟩
  | 3 => ⟨((783615986195117/1125899906842624), (-173126936737013/2251799813685248)), (1707807/281474976710656), by norm_num⟩
  | 4 => ⟨((538734194823363/1125899906842624), (-240989513265991/2251799813685248)), (5279683/562949953421312), by norm_num⟩
  | 5 => ⟨((122442299097939/562949953421312), (-230623149715519/2251799813685248)), (12365291/1125899906842624), by norm_num⟩
  | 6 => ⟨((663244849439763/18014398509481984), (-100321630740923/2251799813685248)), (63294161/9007199254740992), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95658131/33554432), (-752667217/16777216)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-6047887/2097152), (-47586611/1048576)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((171382057862227/18014398509481984), (-248163745885509/4503599627370496)), (155186107/18014398509481984), by norm_num⟩
  | 1 => ⟨((-269340183/8589934592), (1560034223/8589934592)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((110962663/2147483648), (-40168893/134217728)), (51/1073741824), by norm_num⟩
  | 3 => ⟨((-121904945/2147483648), (1412161263/4294967296)), (113/2147483648), by norm_num⟩
  | 4 => ⟨((100444703/2147483648), (-145445411/536870912)), (47/1073741824), by norm_num⟩
  | 5 => ⟨((-66209871/2147483648), (191745739/1073741824)), (125/4294967296), by norm_num⟩
  | 6 => ⟨((36369489/2147483648), (-1685233801/17179869184)), (277/17179869184), by norm_num⟩
  | 7 => ⟨((-273983777/34359738368), (1586930197/34359738368)), (263/34359738368), by norm_num⟩
  | 8 => ⟨((112875729/34359738368), (-653782881/34359738368)), (219/68719476736), by norm_num⟩
  | 9 => ⟨((-165342217/137438953472), (239417969/34359738368)), (81/68719476736), by norm_num⟩
  | 10 => ⟨((108988195/274877906944), (-631266055/274877906944)), (215/549755813888), by norm_num⟩
  | 11 => ⟨((-261241681/2199023255552), (756563613/1099511627776)), (65/549755813888), by norm_num⟩
  | 12 => ⟨((287003321/8796093022208), (-1662340165/8796093022208)), (9/274877906944), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395054805263161/2535301200456458802993406410752), (-1823436905755/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777519926311819/633825300114114700748351602688), (-2155060755777/633825300114114700748351602688)), (92413/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888337117664085/39614081257132168796771975168), (-2423841419083/39614081257132168796771975168)), (51989/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944012329726385/1237940039285380274899124224), (-2574574111821/2475880078570760549798248448)), (110493/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769691206231027/154742504910672534362390528), (-1286861235385/77371252455336267181195264)), (110511/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774073988801545/4835703278458516698824704), (-2411960315463/9671406556917033397649408)), (103623/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257559232595547/604462909807314587353088), (-2109561188961/604462909807314587353088)), (90689/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942897389524799/37778931862957161709568), (-3426342647733/75557863725914323419136)), (36851/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296042021407223/4722366482869645213696), (-2568275365455/4722366482869645213696)), (110585/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619389986128977/590295810358705651712), (-3528972640495/590295810358705651712)), (19013/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910451608632943/36893488147419103232), (-2203804849327/36893488147419103232)), (95103/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909882892484001/4611686018427387904), (-309600449661/576460752303423488)), (214087/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795508216012193/576460752303423488), (-4947422053031/1152921504606846976)), (107109/576460752303423488), by norm_num⟩
  | 5 => ⟨((297996230123727/36028797018963968), (-1080511407927/36028797018963968)), (46897/36028797018963968), by norm_num⟩
  | 4 => ⟨((1487748451997133/36028797018963968), (-3234597567167/18014398509481984)), (281677/36028797018963968), by norm_num⟩
  | 3 => ⟨((742202457537003/4503599627370496), (-8062269566321/9007199254740992)), (176307/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218267800435127/4503599627370496), (-8026040707823/2251799813685248)), (353393/2251799813685248), by norm_num⟩
  | 1 => ⟨((2201646392673889/2251799813685248), (-186701011711/17592186044416)), (1064091/2251799813685248), by norm_num⟩
  | 0 => ⟨((134504395867037/140737488355328), (-2942398901877/140737488355328)), (2143923/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((134504395867037/140737488355328), (-2942398901877/140737488355328)), (8178417214400481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1027886741909403/1125899906842624), (-44993338030599/1125899906842624)), (2093795/1125899906842624), by norm_num⟩
  | 2 => ⟨((1873215811311709/2251799813685248), (-20538262484449/281474976710656)), (7980785/2251799813685248), by norm_num⟩
  | 3 => ⟨((386573104781613/562949953421312), (-273364250508763/2251799813685248)), (3610673/562949953421312), by norm_num⟩
  | 4 => ⟨((16072506048235/35184372088832), (-93858491694717/562949953421312)), (5835497/562949953421312), by norm_num⟩
  | 5 => ⟨((203648294346883/1125899906842624), (-686005103235199/4503599627370496)), (58218119/4503599627370496), by norm_num⟩
  | 6 => ⟨((171382057862227/18014398509481984), (-248163745885509/4503599627370496)), (155186107/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-6047887/2097152), (-47586611/1048576)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile042Terms3
