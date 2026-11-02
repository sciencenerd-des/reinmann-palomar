/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile021Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨21,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6063/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6063/640))
  have he : value ((3/4), (6063/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-622309043/268435456), (-3930270549/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-118187424662449/2251799813685248), (375076763404667/4503599627370496)), (4998927/2251799813685248), by norm_num⟩
  | 1 => ⟨((2787188317/17179869184), (-4422676845/17179869184)), (15/2147483648), by norm_num⟩
  | 2 => ⟨((-2153829353/8589934592), (3417670471/8589934592)), (95/8589934592), by norm_num⟩
  | 3 => ⟨((138699541/536870912), (-3521388173/8589934592)), (25/2147483648), by norm_num⟩
  | 4 => ⟨((-857452339/4294967296), (680297521/2147483648)), (79/8589934592), by norm_num⟩
  | 5 => ⟨((2120337265/17179869184), (-3364525629/17179869184)), (25/4294967296), by norm_num⟩
  | 6 => ⟨((-2184684167/34359738368), (1733315259/17179869184)), (105/34359738368), by norm_num⟩
  | 7 => ⟨((482353679/17179869184), (-3061572029/68719476736)), (47/34359738368), by norm_num⟩
  | 8 => ⟨((-2981951399/274877906944), (2365862279/137438953472)), (147/274877906944), by norm_num⟩
  | 9 => ⟨((2048297415/549755813888), (-101569177/17179869184)), (103/549755813888), by norm_num⟩
  | 10 => ⟨((-2532549707/2199023255552), (4018619367/2199023255552)), (129/2199023255552), by norm_num⟩
  | 11 => ⟨((2846624967/8796093022208), (-2258495103/4398046511104)), (147/8796093022208), by norm_num⟩
  | 12 => ⟨((-1466506437/17592186044416), (581758687/4398046511104)), (153/35184372088832), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580955946170575/10141204801825835211973625643008), (2778638743417/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778387749071979/633825300114114700748351602688), (1643526062751/316912650057057350374175801344)), (5783/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236164126367985/4951760157141521099596496896), (1848588986209/19807040628566084398385987584)), (6507/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236132628458853/309485009821345068724781056), (981830408725/618970019642690137449562112)), (13831/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770726991595193/154742504910672534362390528), (981568921735/38685626227668133590597632)), (6917/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549118407399797/9671406556917033397649408), (3679772421013/9671406556917033397649408)), (6487/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258407740022955/604462909807314587353088), (3218690152411/604462909807314587353088)), (11355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887172444377155/75557863725914323419136), (5228289584119/75557863725914323419136)), (18459/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648537128391335/2361183241434822606848), (244962262035/295147905179352825856)), (13851/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405201915995023/147573952589676412928), (5386211919661/590295810358705651712)), (19053/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822672848242913/73786976294838206464), (3364165179335/36893488147419103232)), (23831/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910876616208631/4611686018427387904), (945409722199/1152921504606846976)), (26829/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398249912734735/288230376151711744), (1888916464581/288230376151711744)), (13427/576460752303423488), by norm_num⟩
  | 5 => ⟨((298428871948547/36028797018963968), (412665729703/9007199254740992)), (11763/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490334824047335/36028797018963968), (1235860531467/4503599627370496)), (2209/2251799813685248), by norm_num⟩
  | 3 => ⟨((743810668053591/4503599627370496), (12328734033347/9007199254740992)), (22139/4503599627370496), by norm_num⟩
  | 2 => ⟨((4345021848175/8796093022208), (3071002731053/562949953421312)), (88849/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105549222438053/1125899906842624), (36629003568291/2251799813685248)), (33503/562949953421312), by norm_num⟩
  | 0 => ⟨((2170486004877287/2251799813685248), (72369405555825/2251799813685248)), (16937/140737488355328), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2170486004877287/2251799813685248), (72369405555825/2251799813685248)), (64609528124761537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2089782643158805/2251799813685248), (69756103977617/1125899906842624)), (67479/281474976710656), by norm_num⟩
  | 2 => ⟨((1930779020877463/2251799813685248), (16184286727095/140737488355328)), (1068875/2251799813685248), by norm_num⟩
  | 3 => ⟨((1625745430021981/2251799813685248), (444064785377529/2251799813685248)), (1039411/1125899906842624), by norm_num⟩
  | 4 => ⟨((1086177667641837/2251799813685248), (160302059506725/562949953421312)), (1910813/1125899906842624), by norm_num⟩
  | 5 => ⟨((682684061432947/4503599627370496), (1237172264106317/4503599627370496)), (2931621/1125899906842624), by norm_num⟩
  | 6 => ⟨((-118187424662449/2251799813685248), (375076763404667/4503599627370496)), (4998927/2251799813685248), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-622309043/268435456), (-3930270549/134217728)), (1/134217728), by norm_num⟩, -5, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-157814591/67108864), (-1993395555/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-241424235400837/18014398509481984), (849080232682983/9007199254740992)), (35994669/9007199254740992), by norm_num⟩
  | 1 => ⟨((721916479/17179869184), (-634738483/2147483648)), (217/17179869184), by norm_num⟩
  | 2 => ⟨((-141472809/2147483648), (995109421/2147483648)), (171/8589934592), by norm_num⟩
  | 3 => ⟨((295724783/4294967296), (-520026639/1073741824)), (181/8589934592), by norm_num⟩
  | 4 => ⟨((-927243347/17179869184), (6522162075/17179869184)), (143/8589934592), by norm_num⟩
  | 5 => ⟨((290736615/8589934592), (-1022510073/4294967296)), (181/17179869184), by norm_num⟩
  | 6 => ⟨((-151933829/8589934592), (4274765893/34359738368)), (191/34359738368), by norm_num⟩
  | 7 => ⟨((544443019/68719476736), (-3829572495/68719476736)), (173/68719476736), by norm_num⟩
  | 8 => ⟨((-106693621/34359738368), (1500950301/68719476736)), (137/137438953472), by norm_num⟩
  | 9 => ⟨((74341607/68719476736), (-522913443/68719476736)), (3/8589934592), by norm_num⟩
  | 10 => ⟨((-186478143/549755813888), (5246694643/2199023255552)), (121/1099511627776), by norm_num⟩
  | 11 => ⟨((53154649/549755813888), (-2991087401/4398046511104)), (139/4398046511104), by norm_num⟩
  | 12 => ⟨((-888885837/35184372088832), (6252358163/35184372088832)), (293/35184372088832), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580912518636921/10141204801825835211973625643008), (1115047327497/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778338436722497/633825300114114700748351602688), (2637994557761/633825300114114700748351602688)), (5779/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944628830681539/19807040628566084398385987584), (185445796885/2475880078570760549798248448)), (26009/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236125298071911/309485009821345068724781056), (3151821916423/2475880078570760549798248448)), (3455/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770668534906753/154742504910672534362390528), (1575485490767/77371252455336267181195264)), (27645/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549063802180391/9671406556917033397649408), (2953131445191/9671406556917033397649408)), (25923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258360158234015/604462909807314587353088), (2583086466331/604462909807314587353088)), (22689/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887095494489691/75557863725914323419136), (2097910998007/37778931862957161709568)), (36879/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648508434128807/2361183241434822606848), (1572692657565/2361183241434822606848)), (27669/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810364640245883/295147905179352825856), (135078096533/18446744073709551616)), (9515/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822575656453851/73786976294838206464), (5399517383889/73786976294838206464)), (47599/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910822486447177/4611686018427387904), (3034750781833/4611686018427387904)), (13395/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796446370231061/576460752303423488), (3031656157137/576460752303423488)), (13405/288230376151711744), by norm_num⟩
  | 5 => ⟨((596811727682743/72057594037927936), (5298442400955/144115188075855872)), (23481/72057594037927936), by norm_num⟩
  | 4 => ⟨((745099897648995/18014398509481984), (7933769418687/36028797018963968)), (17633/9007199254740992), by norm_num⟩
  | 3 => ⟨((185932226963303/1125899906842624), (2473234109593/2251799813685248)), (22081/2251799813685248), by norm_num⟩
  | 2 => ⟨((139021241570719/281474976710656), (9856602312647/2251799813685248)), (177119/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210670493825137/2251799813685248), (918396487833/70368744177664)), (133433/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084892310220569/1125899906842624), (58056199032965/2251799813685248)), (134625/562949953421312), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1084892310220569/1125899906842624), (58056199032965/2251799813685248)), (513553621532249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((32644684017485/35184372088832), (218522158325/4398046511104)), (532771/1125899906842624), by norm_num⟩
  | 2 => ⟨((1932893193672469/2251799813685248), (103807350523689/1125899906842624)), (260393/281474976710656), by norm_num⟩
  | 3 => ⟨((1640009121419423/2251799813685248), (89105843273001/562949953421312)), (495047/281474976710656), by norm_num⟩
  | 4 => ⟨((1138019588543593/2251799813685248), (64896708335867/281474976710656)), (7022493/2251799813685248), by norm_num⟩
  | 5 => ⟨((910868969341801/4503599627370496), (1049524560673617/4503599627370496)), (20672581/4503599627370496), by norm_num⟩
  | 6 => ⟨((-241424235400837/18014398509481984), (849080232682983/9007199254740992)), (35994669/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-157814591/67108864), (-1993395555/67108864)), (1/67108864), by norm_num⟩, -5, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-319913373/134217728), (-2020452899/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((430253571111917/18014398509481984), (200583844346407/2251799813685248)), (61353357/18014398509481984), by norm_num⟩
  | 1 => ⟨((-652012353/8589934592), (-2431740779/8589934592)), (47/4294967296), by norm_num⟩
  | 2 => ⟨((518032589/4294967296), (966025387/2147483648)), (151/8589934592), by norm_num⟩
  | 3 => ⟨((-1097556969/8589934592), (-1023360227/2147483648)), (81/4294967296), by norm_num⟩
  | 4 => ⟨((1744047565/17179869184), (3252293889/8589934592)), (65/4294967296), by norm_num⟩
  | 5 => ⟨((-1108535409/17179869184), (-1033596505/4294967296)), (167/17179869184), by norm_num⟩
  | 6 => ⟨((1174328401/34359738368), (4379767109/34359738368)), (89/17179869184), by norm_num⟩
  | 7 => ⟨((-1066308249/68719476736), (-497111987/8589934592)), (163/68719476736), by norm_num⟩
  | 8 => ⟨((1694392507/274877906944), (6319394617/274877906944)), (131/137438953472), by norm_num⟩
  | 9 => ⟨((-598318955/274877906944), (-557871563/68719476736)), (187/549755813888), by norm_num⟩
  | 10 => ⟨((1521191877/2199023255552), (709178343/274877906944)), (15/137438953472), by norm_num⟩
  | 11 => ⟨((-878987213/4398046511104), (-6556529307/8796093022208)), (279/8796093022208), by norm_num⟩
  | 12 => ⟨((465578113/8796093022208), (1736416923/8796093022208)), (75/8796093022208), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98804433728147/633825300114114700748351602688), (852450038351/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222286350411809/79228162514264337593543950336), (2016631930617/633825300114114700748351602688)), (23101/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889204171470397/39614081257132168796771975168), (283529973951/4951760157141521099596496896)), (25991/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888945679475237/2475880078570760549798248448), (1204709383379/1237940039285380274899124224)), (6905/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770611973579685/154742504910672534362390528), (2408759754615/154742504910672534362390528)), (3453/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549010928592811/9671406556917033397649408), (1128756149655/4835703278458516698824704)), (12951/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258314046386363/604462909807314587353088), (987311774873/302231454903657293676544)), (5667/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887020848508161/75557863725914323419136), (400931482143/9444732965739290427392)), (9211/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((40530035424275/147573952589676412928), (2404441956917/4722366482869645213696)), (3455/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620653050781777/590295810358705651712), (3304244948461/590295810358705651712)), (38017/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822480976730563/73786976294838206464), (4127513871191/73786976294838206464)), (47539/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910769646050747/4611686018427387904), (9061751161/18014398509481984)), (53505/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796394050046657/576460752303423488), (4634825335287/1152921504606846976)), (53535/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596766531424075/72057594037927936), (4050088017925/144115188075855872)), (46879/144115188075855872), by norm_num⟩
  | 4 => ⟨((372516633866155/9007199254740992), (189511835949/1125899906842624)), (35193/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487295301591621/9007199254740992), (3780844482697/4503599627370496)), (44051/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112013479597135/2251799813685248), (15067159341107/4503599627370496)), (176567/4503599627370496), by norm_num⟩
  | 1 => ⟨((276278904031349/281474976710656), (22460663458639/2251799813685248)), (265759/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169025241688413/2251799813685248), (44363842429331/2251799813685248)), (535173/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2169025241688413/2251799813685248), (44363842429331/2251799813685248)), (2041522988326262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2088419370134879/2251799813685248), (42733058890357/1125899906842624)), (1052089/2251799813685248), by norm_num⟩
  | 2 => ⟨((1933649244397121/2251799813685248), (158530163097723/2251799813685248)), (507843/562949953421312), by norm_num⟩
  | 3 => ⟨((1649288522529775/2251799813685248), (272263749401759/2251799813685248)), (3774755/2251799813685248), by norm_num⟩
  | 4 => ⟨((587535593801235/1125899906842624), (398828949412117/2251799813685248)), (6442305/2251799813685248), by norm_num⟩
  | 5 => ⟨((542556117830409/2251799813685248), (832493908894957/4503599627370496)), (18011451/4503599627370496), by norm_num⟩
  | 6 => ⟨((430253571111917/18014398509481984), (200583844346407/2251799813685248)), (61353357/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-319913373/134217728), (-2020452899/67108864)), (1/67108864), by norm_num⟩, -5, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-162011325/67108864), (-4092811097/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((486713956827803/9007199254740992), (626939914665/8796093022208)), (12441447/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2988189295/17179869184), (-985371941/4294967296)), (79/17179869184), by norm_num⟩
  | 2 => ⟨((2404652571/8589934592), (3171789919/8589934592)), (33/4294967296), by norm_num⟩
  | 3 => ⟨((-645023169/2147483648), (-3403199297/8589934592)), (73/8589934592), by norm_num⟩
  | 4 => ⟨((2076249485/8589934592), (1369309493/4294967296)), (15/2147483648), by norm_num⟩
  | 5 => ⟨((-1336637855/8589934592), (-3526109779/17179869184)), (79/17179869184), by norm_num⟩
  | 6 => ⟨((2868314185/34359738368), (3783369841/34359738368)), (87/34359738368), by norm_num⟩
  | 7 => ⟨((-329740971/8589934592), (-1739742531/34359738368)), (41/34359738368), by norm_num⟩
  | 8 => ⟨((132674405/8589934592), (2800007587/137438953472)), (17/34359738368), by norm_num⟩
  | 9 => ⟨((-1518444213/274877906944), (-250357687/34359738368)), (25/137438953472), by norm_num⟩
  | 10 => ⟨((1955073347/1099511627776), (644696245/274877906944)), (33/549755813888), by norm_num⟩
  | 11 => ⟨((-2288413939/4398046511104), (-3018468593/4398046511104)), (79/4398046511104), by norm_num⟩
  | 12 => ⟨((2455373435/17592186044416), (3238691861/17592186044416)), (87/17592186044416), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98801941140089/633825300114114700748351602688), (1201148089451/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222280591059517/79228162514264337593543950336), (1420699762647/633825300114114700748351602688)), (1443/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889152409348481/39614081257132168796771975168), (798976156449/19807040628566084398385987584)), (3247/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888890776550111/2475880078570760549798248448), (1697406315661/2475880078570760549798248448)), (13801/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770557176678787/154742504910672534362390528), (1696936246175/154742504910672534362390528)), (6901/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548959669073559/9671406556917033397649408), (198797307171/1208925819614629174706176)), (12941/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39320915837421/18889465931478580854784), (695541037079/302231454903657293676544)), (11325/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943474178707779/37778931862957161709568), (2259573022185/75557863725914323419136)), (18405/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296906949474147/4722366482869645213696), (1693861755899/4722366482869645213696)), (13807/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620578846655469/590295810358705651712), (1163865716085/295147905179352825856)), (4747/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455597167376237/18446744073709551616), (2907672940247/73786976294838206464)), (23741/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455359015355465/2305843009213693952), (1634198090781/4611686018427387904)), (26717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398171409166367/288230376151711744), (1632489839185/576460752303423488)), (3341/144115188075855872), by norm_num⟩
  | 5 => ⟨((596722134268663/72057594037927936), (356627280391/18014398509481984)), (2925/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489935061460095/36028797018963968), (2135930438147/18014398509481984)), (35123/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487133953608899/9007199254740992), (665804436561/1125899906842624)), (21973/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223713202779765/4503599627370496), (10612801989955/4503599627370496)), (88019/4503599627370496), by norm_num⟩
  | 1 => ⟨((69055712281043/70368744177664), (61794490137/8796093022208)), (66175/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084108113968237/1125899906842624), (15620835916217/1125899906842624)), (132997/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1084108113968237/1125899906842624), (15620835916217/1125899906842624)), (507343296531295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1043650847749197/1125899906842624), (30082025694855/1125899906842624)), (519623/2251799813685248), by norm_num⟩
  | 2 => ⟨((1933212991889575/2251799813685248), (27884478387151/562949953421312)), (991095/2251799813685248), by norm_num⟩
  | 3 => ⟨((1654175359289963/2251799813685248), (47878710676223/562949953421312)), (449983/562949953421312), by norm_num⟩
  | 4 => ⟨((1198871306365223/2251799813685248), (140687076984103/1125899906842624)), (2950633/2251799813685248), by norm_num⟩
  | 5 => ⟨((603126879419117/2251799813685248), (599220938726703/4503599627370496)), (3879263/2251799813685248), by norm_num⟩
  | 6 => ⟨((486713956827803/9007199254740992), (626939914665/8796093022208)), (12441447/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/67108864), (-4092811097/134217728)), (1/134217728), by norm_num⟩, -5, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-20498171/8388608), (-2071340181/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((333341518892605/4503599627370496), (818507843543959/18014398509481984)), (38460725/18014398509481984), by norm_num⟩
  | 1 => ⟨((-517873215/2147483648), (-2543237277/17179869184)), (61/8589934592), by norm_num⟩
  | 2 => ⟨((1687280929/4294967296), (1035764071/4294967296)), (101/8589934592), by norm_num⟩
  | 3 => ⟨((-3664882769/8589934592), (-2249746223/8589934592)), (111/8589934592), by norm_num⟩
  | 4 => ⟨((2985135465/8589934592), (1832472595/8589934592)), (23/2147483648), by norm_num⟩
  | 5 => ⟨((-1945171905/8589934592), (-2388149047/17179869184)), (61/8589934592), by norm_num⟩
  | 6 => ⟨((2112519283/17179869184), (1296803357/17179869184)), (67/17179869184), by norm_num⟩
  | 7 => ⟨((-491627983/8589934592), (-2414348873/68719476736)), (127/68719476736), by norm_num⟩
  | 8 => ⟨((3203542859/137438953472), (983272713/68719476736)), (105/137438953472), by norm_num⟩
  | 9 => ⟨((-2319433755/274877906944), (-2847642153/549755813888)), (77/274877906944), by norm_num⟩
  | 10 => ⟨((3022775635/1099511627776), (115973663/68719476736)), (51/549755813888), by norm_num⟩
  | 11 => ⟨((-55957357/68719476736), (-2198419723/4398046511104)), (61/2199023255552), by norm_num⟩
  | 12 => ⟨((486171923/2199023255552), (2387554563/17592186044416)), (67/8796093022208), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395198185306375/2535301200456458802993406410752), (179289061507/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778200104841225/633825300114114700748351602688), (424100170287/316912650057057350374175801344)), (721/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1889102257086573/39614081257132168796771975168), (954023508387/39614081257132168796771975168)), (25957/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944418777127383/1237940039285380274899124224), (1013397417537/2475880078570760549798248448)), (27581/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885252013430367/77371252455336267181195264), (506556708143/77371252455336267181195264)), (27583/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774454959037765/4835703278458516698824704), (949492187223/9671406556917033397649408)), (25861/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629112925786739/302231454903657293676544), (830504147955/604462909807314587353088)), (11315/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235859735842679/9444732965739290427392), (1349004162997/75557863725914323419136)), (36777/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296854222404115/4722366482869645213696), (126407368021/590295810358705651712)), (13793/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202563318919053/73786976294838206464), (1389678504809/590295810358705651712)), (37935/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822298606606591/73786976294838206464), (1735895183195/73786976294838206464)), (23713/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821335161083821/9223372036854775808), (975614718047/4611686018427387904)), (53365/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592585260890605/1152921504606846976), (1949165740223/1152921504606846976)), (26689/576460752303423488), by norm_num⟩
  | 5 => ⟨((298339257135751/36028797018963968), (1703201263373/144115188075855872)), (365/1125899906842624), by norm_num⟩
  | 4 => ⟨((744902687890035/18014398509481984), (1275085806527/18014398509481984)), (70109/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486973894132941/9007199254740992), (1589813889303/4503599627370496)), (87687/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223399197102627/4503599627370496), (1583765058581/1125899906842624)), (175529/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209326964461607/2251799813685248), (1180291070381/281474976710656)), (131841/1125899906842624), by norm_num⟩
  | 0 => ⟨((2167364674685201/2251799813685248), (9322482160203/1125899906842624)), (264467/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2167364674685201/2251799813685248), (9322482160203/1125899906842624)), (1008861546043014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2085941196829379/2251799813685248), (35891678099643/2251799813685248)), (513481/1125899906842624), by norm_num⟩
  | 2 => ⟨((965863492313351/1125899906842624), (16624019932051/562949953421312)), (1935379/2251799813685248), by norm_num⟩
  | 3 => ⟨((413796487576751/562949953421312), (28522133895339/562949953421312)), (1717435/1125899906842624), by norm_num⟩
  | 4 => ⟨((1210864446995519/2251799813685248), (167721606545755/2251799813685248)), (168677/70368744177664), by norm_num⟩
  | 5 => ⟨((1277255787087017/4503599627370496), (90189247341155/1125899906842624)), (826133/281474976710656), by norm_num⟩
  | 6 => ⟨((333341518892605/4503599627370496), (818507843543959/18014398509481984)), (38460725/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20498171/8388608), (-2071340181/67108864)), (1/67108864), by norm_num⟩, -5, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-165884901/67108864), (-261916707/8388608)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((93290164334361/1125899906842624), (72936271466911/4503599627370496)), (7060711/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4691607099/17179869184), (-917000017/17179869184)), (45/8589934592), by norm_num⟩
  | 2 => ⟨((3865692909/8589934592), (94446327/1073741824)), (19/2147483648), by norm_num⟩
  | 3 => ⟨((-2123448867/4294967296), (-207519791/2147483648)), (85/8589934592), by norm_num⟩
  | 4 => ⟨((6998541059/17179869184), (1367902755/17179869184)), (71/8589934592), by norm_num⟩
  | 5 => ⟨((-2306604963/8589934592), (-450838433/8589934592)), (95/17179869184), by norm_num⟩
  | 6 => ⟨((5068129115/34359738368), (990593285/34359738368)), (53/17179869184), by norm_num⟩
  | 7 => ⟨((-4772493365/68719476736), (-932809677/68719476736)), (51/34359738368), by norm_num⟩
  | 8 => ⟨((1966169947/68719476736), (768597131/137438953472)), (43/68719476736), by norm_num⟩
  | 9 => ⟨((-1440038977/137438953472), (-1125853671/549755813888)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((3796906839/1099511627776), (742126007/1099511627776)), (43/549755813888), by norm_num⟩
  | 11 => ⟨((-4550540195/4398046511104), (-55589233/274877906944)), (105/4398046511104), by norm_num⟩
  | 12 => ⟨((2499639689/8796093022208), (122142029/2199023255552)), (117/17592186044416), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (62858167695/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778156836003837/633825300114114700748351602688), (297362408271/633825300114114700748351602688)), (11529/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472263402197123/9903520314283042199192993792), (83615306935/9903520314283042199192993792)), (25941/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888785903305165/2475880078570760549798248448), (44409436931/309485009821345068724781056)), (27563/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885226209237557/77371252455336267181195264), (177587394519/77371252455336267181195264)), (27563/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548861580410261/9671406556917033397649408), (166434702247/4835703278458516698824704)), (25841/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258183601281111/604462909807314587353088), (145576907047/302231454903657293676544)), (5653/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886809314633327/75557863725914323419136), (472924578993/75557863725914323419136)), (36745/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324200716824013/1180591620717411303424), (354518207803/4722366482869645213696)), (3445/590295810358705651712), by norm_num⟩
  | 9 => ⟨((202554507269969/73786976294838206464), (7612155833/9223372036854775808)), (37897/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822210670018177/73786976294838206464), (608545938747/73786976294838206464)), (23687/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821236479432321/9223372036854775808), (684028217869/9223372036854775808)), (53299/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592486887469851/1152921504606846976), (341648266017/576460752303423488)), (6663/144115188075855872), by norm_num⟩
  | 5 => ⟨((298317824457161/36028797018963968), (597062373999/144115188075855872)), (23323/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489677469942657/36028797018963968), (893952011841/36028797018963968)), (34989/18014398509481984), by norm_num⟩
  | 3 => ⟨((743407607826359/4503599627370496), (1114573219947/9007199254740992)), (21873/2251799813685248), by norm_num⟩
  | 2 => ⟨((2223085435267115/4503599627370496), (2220569669555/4503599627370496)), (2735/70368744177664), by norm_num⟩
  | 1 => ⟨((552216313149943/562949953421312), (3309495001653/2251799813685248)), (262705/2251799813685248), by norm_num⟩
  | 0 => ⟨((270809579340049/281474976710656), (3267022361775/1125899906842624)), (263001/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((270809579340049/281474976710656), (3267022361775/1125899906842624)), (1003269199851607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1042183742649737/1125899906842624), (12572925122169/2251799813685248)), (253799/562949953421312), by norm_num⟩
  | 2 => ⟨((1929314368410717/2251799813685248), (11638066652499/1125899906842624)), (236345/281474976710656), by norm_num⟩
  | 3 => ⟨((1652772209659053/2251799813685248), (19942704566123/1125899906842624)), (3279049/2251799813685248), by norm_num⟩
  | 4 => ⟨((303098116733971/562949953421312), (29275024975143/1125899906842624)), (38513/17592186044416), by norm_num⟩
  | 5 => ⟨((651242342512547/2251799813685248), (63047913111133/2251799813685248)), (2782361/1125899906842624), by norm_num⟩
  | 6 => ⟨((93290164334361/1125899906842624), (72936271466911/4503599627370496)), (7060711/4503599627370496), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-261916707/8388608)), (1/67108864), by norm_num⟩, -5, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile021Terms3
