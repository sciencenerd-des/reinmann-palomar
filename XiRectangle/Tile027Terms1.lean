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
namespace Reinmann.XiRectangle.Tile027Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨27,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7473/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (7473/640))
  have he : value ((5/8), (7473/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-368633113/268435456), (-1721747035/67108864)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((988021772725669/4503599627370496), (-570026457879485/4503599627370496)), (2535665/562949953421312), by norm_num⟩
  | 1 => ⟨((-4140674061/8589934592), (2388908659/8589934592)), (87/8589934592), by norm_num⟩
  | 2 => ⟨((4548995407/8589934592), (-2624484409/8589934592)), (49/4294967296), by norm_num⟩
  | 3 => ⟨((-104116297/268435456), (961096941/4294967296)), (37/4294967296), by norm_num⟩
  | 4 => ⟨((3660270187/17179869184), (-527936455/4294967296)), (83/17179869184), by norm_num⟩
  | 5 => ⟨((-1608487123/17179869184), (1855991927/34359738368)), (75/34359738368), by norm_num⟩
  | 6 => ⟨((4712276585/137438953472), (-2718687385/137438953472)), (7/8589934592), by norm_num⟩
  | 7 => ⟨((-1479132847/137438953472), (853366677/137438953472)), (73/274877906944), by norm_num⟩
  | 8 => ⟨((3249987045/1099511627776), (-468759559/274877906944)), (41/549755813888), by norm_num⟩
  | 9 => ⟨((-3173756183/4398046511104), (457764455/1099511627776)), (41/2199023255552), by norm_num⟩
  | 10 => ⟨((2789382035/17592186044416), (-804649049/8796093022208)), (37/8796093022208), by norm_num⟩
  | 11 => ⟨((-4457380919/140737488355328), (1285814303/70368744177664)), (121/140737488355328), by norm_num⟩
  | 12 => ⟨((1632311151/281474976710656), (-1883481859/562949953421312)), (45/281474976710656), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582186935648693/10141204801825835211973625643008), (-681642184993/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779850551268133/633825300114114700748351602688), (-807621822023/633825300114114700748351602688)), (17303/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118184918775039/2475880078570760549798248448), (-908463782515/39614081257132168796771975168)), (19467/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890809644012105/2475880078570760549798248448), (-482553754331/1237940039285380274899124224)), (5171/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((443118921957465/38685626227668133590597632), (-964955373489/154742504910672534362390528)), (10343/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550757894771575/9671406556917033397649408), (-226121012839/2417851639229258349412352)), (19395/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259842375860603/604462909807314587353088), (-791261970017/604462909807314587353088)), (16971/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889503885278085/75557863725914323419136), (-1285497825573/75557863725914323419136)), (27581/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649411487426985/2361183241434822606848), (-481929215093/2361183241434822606848)), (1293/295147905179352825856), by norm_num⟩
  | 9 => ⟨((811606186772489/295147905179352825856), (-1324874960433/590295810358705651712)), (28449/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825679066686991/73786976294838206464), (-1655448382225/73786976294838206464)), (35567/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825135680980841/9223372036854775808), (-1861492528747/9223372036854775808)), (10005/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596382661053451/1152921504606846976), (-1860384519013/1152921504606846976)), (40029/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196676247258043/144115188075855872), (-1626590790841/144115188075855872)), (8759/36028797018963968), by norm_num⟩
  | 4 => ⟨((373694299793419/9007199254740992), (-2437396977325/36028797018963968)), (26287/18014398509481984), by norm_num⟩
  | 3 => ⟨((1493176433561285/9007199254740992), (-1521197433329/4503599627370496)), (65753/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235767629909515/4503599627370496), (-3035877345251/2251799813685248)), (32903/1125899906842624), by norm_num⟩
  | 1 => ⟨((2227788254936499/2251799813685248), (-283597216085/70368744177664)), (197689/2251799813685248), by norm_num⟩
  | 0 => ⟨((2203923355193093/2251799813685248), (-9010267764589/1125899906842624)), (396467/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2203923355193093/2251799813685248), (-9010267764589/1125899906842624)), (1512401589400481467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2156920604729971/2251799813685248), (-2204674172437/140737488355328)), (391211/1125899906842624), by norm_num⟩
  | 2 => ⟨((1032743265245231/1125899906842624), (-67576979024087/2251799813685248)), (47607/70368744177664), by norm_num⟩
  | 3 => ⟨((1892560756797003/2251799813685248), (-61985678787785/1125899906842624)), (1443095/1125899906842624), by norm_num⟩
  | 4 => ⟨((395951862482859/562949953421312), (-104193687595343/1125899906842624)), (1292321/562949953421312), by norm_num⟩
  | 5 => ⟨((1094689112832483/2251799813685248), (-293139270456303/2251799813685248)), (8228409/2251799813685248), by norm_num⟩
  | 6 => ⟨((988021772725669/4503599627370496), (-570026457879485/4503599627370496)), (2535665/562949953421312), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-368633113/268435456), (-1721747035/67108864)), (3/268435456), by norm_num⟩, -4, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-386309675/268435456), (-225538453/8388608)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6064938367261/140737488355328), (-1050189233187317/4503599627370496)), (2091775/281474976710656), by norm_num⟩
  | 1 => ⟨((852358195/8589934592), (1153063809/2147483648)), (149/8589934592), by norm_num⟩
  | 2 => ⟨((-981313637/8589934592), (-5310055075/8589934592)), (87/4294967296), by norm_num⟩
  | 3 => ⟨((753186051/8589934592), (2037808943/4294967296)), (135/8589934592), by norm_num⟩
  | 4 => ⟨((-867137487/17179869184), (-2346114247/8589934592)), (79/8589934592), by norm_num⟩
  | 5 => ⟨((199665785/8589934592), (4321702153/34359738368)), (147/34359738368), by norm_num⟩
  | 6 => ⟨((-1225993227/137438953472), (-6634057969/137438953472)), (57/34359738368), by norm_num⟩
  | 7 => ⟨((1575309/536870912), (2182211855/137438953472)), (19/34359738368), by norm_num⟩
  | 8 => ⟨((-928584453/1099511627776), (-5024728487/1099511627776)), (177/1099511627776), by norm_num⟩
  | 9 => ⟨((475143271/2199023255552), (2571081091/2199023255552)), (183/4398046511104), by norm_num⟩
  | 10 => ⟨((-437623125/8796093022208), (-2368053197/8796093022208)), (85/8796093022208), by norm_num⟩
  | 11 => ⟨((732846897/70368744177664), (1982779633/35184372088832)), (9/4398046511104), by norm_num⟩
  | 12 => ⟨((-140620195/70368744177664), (-3043679217/281474976710656)), (223/562949953421312), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791050579124123/5070602400912917605986812821504), (-2284178403013/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779745363009375/633825300114114700748351602688), (-676510386751/158456325028528675187087900672)), (8669/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890840170239569/39614081257132168796771975168), (-3043902307503/39614081257132168796771975168)), (19509/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890683460541259/2475880078570760549798248448), (-1616835280711/1237940039285380274899124224)), (5183/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772349228679999/154742504910672534362390528), (-808283876975/38685626227668133590597632)), (81/604462909807314587353088), by norm_num⟩
  | 13 => ⟨((775319523272197/4835703278458516698824704), (-3030496108055/9671406556917033397649408)), (4861/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314934522759805/151115727451828646838272), (-2651115735637/604462909807314587353088)), (8509/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889333874097981/75557863725914323419136), (-4306997549833/75557863725914323419136)), (13831/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324673746747151/1180591620717411303424), (-1614657992149/2361183241434822606848)), (10377/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811517805838971/295147905179352825856), (-4438794974941/590295810358705651712)), (28549/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825456947580243/73786976294838206464), (-5546222464005/73786976294838206464)), (4463/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824884194386839/9223372036854775808), (-1559094527643/2305843009213693952)), (20095/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596129173780007/1152921504606846976), (-6232476630045/1152921504606846976)), (40221/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598226099329685/72057594037927936), (-5449029565995/144115188075855872)), (8807/36028797018963968), by norm_num⟩
  | 4 => ⟨((373609160155929/9007199254740992), (-4082386791163/18014398509481984)), (26455/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492742905298761/9007199254740992), (-10190627603773/9007199254740992)), (33129/4503599627370496), by norm_num⟩
  | 2 => ⟨((279359645289011/562949953421312), (-10167637499329/2251799813685248)), (66439/2251799813685248), by norm_num⟩
  | 1 => ⟨((139149643899833/140737488355328), (-7597023716887/562949953421312)), (100111/1125899906842624), by norm_num⟩
  | 0 => ⟨((137556506299741/140737488355328), (-30158859055967/1125899906842624)), (101019/562949953421312), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((137556506299741/140737488355328), (-30158859055967/1125899906842624)), (385356905223655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((268692880932663/281474976710656), (-58954402756585/1125899906842624)), (50721/140737488355328), by norm_num⟩
  | 2 => ⟨((511438982994293/562949953421312), (-14069304228609/140737488355328)), (408589/562949953421312), by norm_num⟩
  | 3 => ⟨((918030835999425/1125899906842624), (-204510986524073/1125899906842624)), (824097/562949953421312), by norm_num⟩
  | 4 => ⟨((711391720852775/1125899906842624), (-41688295466749/140737488355328)), (3286557/1125899906842624), by norm_num⟩
  | 5 => ⟨((701397492702687/2251799813685248), (-210723586146667/562949953421312)), (3050109/562949953421312), by norm_num⟩
  | 6 => ⟨((-6064938367261/140737488355328), (-1050189233187317/4503599627370496)), (2091775/281474976710656), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-386309675/268435456), (-225538453/8388608)), (3/268435456), by norm_num⟩, -4, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-402300069/268435456), (-3757985523/134217728)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-968359766748253/4503599627370496), (-273388501575855/4503599627370496)), (32446259/4503599627370496), by norm_num⟩
  | 1 => ⟨((4428911795/8589934592), (1250375739/8589934592)), (75/4294967296), by norm_num⟩
  | 2 => ⟨((-331877083/536870912), (-1499135037/8589934592)), (91/4294967296), by norm_num⟩
  | 3 => ⟨((530537659/1073741824), (1198256273/8589934592)), (147/8589934592), by norm_num⟩
  | 4 => ⟨((-2544347489/8589934592), (-718323263/8589934592)), (179/17179869184), by norm_num⟩
  | 5 => ⟨((4880863053/34359738368), (1377971165/34359738368)), (87/17179869184), by norm_num⟩
  | 6 => ⟨((-3901266147/68719476736), (-1101410181/68719476736)), (141/68719476736), by norm_num⟩
  | 7 => ⟨((5345615801/274877906944), (377295181/68719476736)), (195/274877906944), by norm_num⟩
  | 8 => ⟨((-3204556715/549755813888), (-904714331/549755813888)), (59/274877906944), by norm_num⟩
  | 9 => ⟨((3415196177/2199023255552), (964182319/2199023255552)), (127/2199023255552), by norm_num⟩
  | 10 => ⟨((-6551426215/17592186044416), (-462401645/4398046511104)), (123/8796093022208), by norm_num⟩
  | 11 => ⟨((1428148541/17592186044416), (403196625/17592186044416)), (217/70368744177664), by norm_num⟩
  | 12 => ⟨((-2283033757/140737488355328), (-322274427/70368744177664)), (175/281474976710656), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197752945394709/1267650600228229401496703205376), (-3733848751071/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779646900992545/633825300114114700748351602688), (-2211507987537/316912650057057350374175801344)), (8685/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890729034525833/39614081257132168796771975168), (-1243801154867/9903520314283042199192993792)), (9773/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890564913541173/2475880078570760549798248448), (-2642671603499/1237940039285380274899124224)), (10387/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110764384903367/9671406556917033397649408), (-5284429885045/154742504910672534362390528)), (20781/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550526862547895/9671406556917033397649408), (-4953182566989/9671406556917033397649408)), (9745/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78727460917759/37778931862957161709568), (-135408257637/18889465931478580854784)), (17061/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889172419364819/75557863725914323419136), (-7039409597391/75557863725914323419136)), (27737/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649286493002433/2361183241434822606848), (-1319491191193/1180591620717411303424)), (10407/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622866382883137/590295810358705651712), (-7254613645073/590295810358705651712)), (28639/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825243197523845/73786976294838206464), (-9064384844421/73786976294838206464)), (35827/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912320342324713/4611686018427387904), (-10192094340117/9223372036854775808)), (20173/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595881868005427/1152921504606846976), (-10185420231811/1152921504606846976)), (40395/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598115771300077/72057594037927936), (-1113091647333/18014398509481984)), (35403/144115188075855872), by norm_num⟩
  | 4 => ⟨((747048573552757/18014398509481984), (-1667759733939/4503599627370496)), (1663/1125899906842624), by norm_num⟩
  | 3 => ⟨((1492303686449127/9007199254740992), (-4162825675489/2251799813685248)), (66717/9007199254740992), by norm_num⟩
  | 2 => ⟨((139622145430469/281474976710656), (-16611848332645/2251799813685248)), (67013/2251799813685248), by norm_num⟩
  | 1 => ⟨((278112451011851/281474976710656), (-24819094135825/1125899906842624)), (101261/1125899906842624), by norm_num⟩
  | 0 => ⟨((549369065978021/562949953421312), (-49243228211151/1125899906842624)), (205501/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((549369065978021/562949953421312), (-49243228211151/1125899906842624)), (783924107078170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((535038940747511/562949953421312), (-48055259839157/562949953421312)), (52383/140737488355328), by norm_num⟩
  | 2 => ⟨((1008819197487333/1125899906842624), (-91345367968959/562949953421312)), (108515/140737488355328), by norm_num⟩
  | 3 => ⟨((218567445969031/281474976710656), (-163692989489715/562949953421312)), (918709/562949953421312), by norm_num⟩
  | 4 => ⟨((583680726654809/1125899906842624), (-1016870744359791/2251799813685248)), (3922097/1125899906842624), by norm_num⟩
  | 5 => ⟨((145975077331743/2251799813685248), (-65894829035733/140737488355328)), (7608821/1125899906842624), by norm_num⟩
  | 6 => ⟨((-968359766748253/4503599627370496), (-273388501575855/4503599627370496)), (32446259/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-402300069/268435456), (-3757985523/134217728)), (3/268435456), by norm_num⟩, -4, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-104224539/67108864), (-973587475/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-175797439773923/1125899906842624), (643151337014679/4503599627370496)), (21496689/4503599627370496), by norm_num⟩
  | 1 => ⟨((416603305/1073741824), (-3048269337/8589934592)), (13/1073741824), by norm_num⟩
  | 2 => ⟨((-4140881291/8589934592), (3787332373/8589934592)), (33/2147483648), by norm_num⟩
  | 3 => ⟨((107184411/268435456), (-3137055799/8589934592)), (7/536870912), by norm_num⟩
  | 4 => ⟨((-2130746045/8589934592), (121801419/536870912)), (71/8589934592), by norm_num⟩
  | 5 => ⟨((4235764013/34359738368), (-3874113997/34359738368)), (143/34359738368), by norm_num⟩
  | 6 => ⟨((-3508492721/68719476736), (3208937211/68719476736)), (15/8589934592), by norm_num⟩
  | 7 => ⟨((2490936255/137438953472), (-2278259833/137438953472)), (87/137438953472), by norm_num⟩
  | 8 => ⟨((-96714751/17179869184), (176914469/34359738368)), (55/274877906944), by norm_num⟩
  | 9 => ⟨((3417985819/2199023255552), (-3126157799/2199023255552)), (31/549755813888), by norm_num⟩
  | 10 => ⟨((-849337569/2199023255552), (3107284121/8796093022208)), (125/8796093022208), by norm_num⟩
  | 11 => ⟨((767463481/8796093022208), (-2807749445/35184372088832)), (115/35184372088832), by norm_num⟩
  | 12 => ⟨((-1271383405/70368744177664), (2325665089/140737488355328)), (97/140737488355328), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581952724385157/10141204801825835211973625643008), (1563628148131/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779566111220639/633825300114114700748351602688), (3704130841111/633825300114114700748351602688)), (11571/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945319170616723/19807040628566084398385987584), (1041639677965/9903520314283042199192993792)), (3255/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890468797527793/2475880078570760549798248448), (2213132600523/1237940039285380274899124224)), (6919/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772134318657179/154742504910672534362390528), (2212736909595/77371252455336267181195264)), (6921/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550437306097733/9671406556917033397649408), (2074020452303/4835703278458516698824704)), (12981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157445163251697/75557863725914323419136), (907173759539/151115727451828646838272)), (5681/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((59032690852501/2361183241434822606848), (5895053125591/75557863725914323419136)), (9235/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298478732469179/4722366482869645213696), (1104977668277/1180591620717411303424)), (3465/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405684391146931/147573952589676412928), (6075136213133/590295810358705651712)), (4767/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825083344180745/73786976294838206464), (7590559157415/73786976294838206464)), (23851/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912231228098053/4611686018427387904), (1066844759097/1152921504606846976)), (13427/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595705645437615/1152921504606846976), (4264491335115/576460752303423488)), (13441/576460752303423488), by norm_num⟩
  | 5 => ⟨((149509950161941/18014398509481984), (466022727723/9007199254740992)), (23553/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493873734083829/36028797018963968), (174555561451/562949953421312)), (553/562949953421312), by norm_num⟩
  | 3 => ⟨((746016137709261/4503599627370496), (6970859848775/4503599627370496)), (22175/4503599627370496), by norm_num⟩
  | 2 => ⟨((34897421859103/70368744177664), (6953822452393/1125899906842624)), (11129/562949953421312), by norm_num⟩
  | 1 => ⟨((1112089550494269/1125899906842624), (10388163242173/562949953421312)), (67187/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098133842051919/1125899906842624), (10303092502705/281474976710656)), (68017/562949953421312), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1098133842051919/1125899906842624), (10303092502705/281474976710656)), (259464266063499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1069543987257937/1125899906842624), (40196022705927/562949953421312)), (137659/562949953421312), by norm_num⟩
  | 2 => ⟨((1010268721758671/1125899906842624), (19092023249815/140737488355328)), (70299/140737488355328), by norm_num⟩
  | 3 => ⟨((221448314719047/281474976710656), (68525004068851/281474976710656)), (1161853/1125899906842624), by norm_num⟩
  | 4 => ⟨((1260323185456117/2251799813685248), (862584480908191/2251799813685248)), (299233/140737488355328), by norm_num⟩
  | 5 => ⟨((374972295478049/2251799813685248), (965570042324535/2251799813685248)), (9027361/2251799813685248), by norm_num⟩
  | 6 => ⟨((-175797439773923/1125899906842624), (643151337014679/4503599627370496)), (21496689/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-104224539/67108864), (-973587475/33554432)), (1/134217728), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215163547/134217728), (-8039585933/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((189394783520759/9007199254740992), (450746332197095/2251799813685248)), (35005589/9007199254740992), by norm_num⟩
  | 1 => ⟨((-231641783/4294967296), (-1102582469/2147483648)), (11/1073741824), by norm_num⟩
  | 2 => ⟨((297074721/4294967296), (5656136391/8589934592)), (115/8589934592), by norm_num⟩
  | 3 => ⟨((-507987743/8589934592), (-2417950567/4294967296)), (25/2147483648), by norm_num⟩
  | 4 => ⟨((651481417/17179869184), (6201920753/17179869184)), (131/17179869184), by norm_num⟩
  | 5 => ⟨((-668406737/34359738368), (-1590761265/8589934592)), (17/4294967296), by norm_num⟩
  | 6 => ⟨((571476477/68719476736), (5440296113/68719476736)), (59/34359738368), by norm_num⟩
  | 7 => ⟨((-418802349/137438953472), (-996720287/34359738368)), (11/17179869184), by norm_num⟩
  | 8 => ⟨((33568963/34359738368), (5113074119/549755813888)), (115/549755813888), by norm_num⟩
  | 9 => ⟨((-153071449/549755813888), (-1457197353/549755813888)), (133/2199023255552), by norm_num⟩
  | 10 => ⟨((78524103/1099511627776), (5980219863/8796093022208)), (139/8796093022208), by norm_num⟩
  | 11 => ⟨((-585921011/35184372088832), (-2788902017/17592186044416)), (33/8796093022208), by norm_num⟩
  | 12 => ⟨((250476287/70368744177664), (4768928291/140737488355328)), (115/140737488355328), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395471889758183/2535301200456458802993406410752), (477451151331/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779493525634811/633825300114114700748351602688), (565478322743/158456325028528675187087900672)), (5777/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236319620169931/4951760157141521099596496896), (636072212349/9903520314283042199192993792)), (1625/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890382684937797/2475880078570760549798248448), (2702864359339/2475880078570760549798248448)), (6907/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772048603594727/154742504910672534362390528), (2702366581881/154742504910672534362390528)), (1727/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193794671300699/1208925819614629174706176), (633234968957/2417851639229258349412352)), (12955/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259491784243637/604462909807314587353088), (2215793702225/604462909807314587353088)), (11339/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888933925116533/75557863725914323419136), (3599673698303/75557863725914323419136)), (18429/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298395287256603/4722366482869645213696), (1349444156835/2361183241434822606848)), (6913/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811311975046443/295147905179352825856), (1854781520843/295147905179352825856)), (19017/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824943008550807/73786976294838206464), (4634841953451/73786976294838206464)), (23781/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824306889565013/9223372036854775808), (5211294601189/9223372036854775808)), (26767/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595552963794893/1152921504606846976), (650958518569/144115188075855872)), (26785/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195949245381777/144115188075855872), (4552632335589/144115188075855872)), (733/4503599627370496), by norm_num⟩
  | 4 => ⟨((746842334273575/18014398509481984), (6820800075337/36028797018963968)), (35221/36028797018963968), by norm_num⟩
  | 3 => ⟨((745903617248753/4503599627370496), (8511754203117/9007199254740992)), (22047/4503599627370496), by norm_num⟩
  | 2 => ⟨((558254668975983/1125899906842624), (8490413073467/2251799813685248)), (22097/1125899906842624), by norm_num⟩
  | 1 => ⟨((277954826739185/281474976710656), (12682363719111/1125899906842624)), (4159/70368744177664), by norm_num⟩
  | 0 => ⟨((274440038454033/281474976710656), (50304570281035/2251799813685248)), (134101/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((274440038454033/281474976710656), (50304570281035/2251799813685248)), (511554722312545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2139523612247679/2251799813685248), (49047302050343/1125899906842624)), (267491/1125899906842624), by norm_num⟩
  | 2 => ⟨((507143075979731/562949953421312), (46601771709899/562949953421312)), (1063227/2251799813685248), by norm_num⟩
  | 3 => ⟨((906021477887299/1125899906842624), (83964003220641/562949953421312)), (522921/562949953421312), by norm_num⟩
  | 4 => ⟨((704036920358801/1125899906842624), (270266263723681/1125899906842624)), (3990343/2251799813685248), by norm_num⟩
  | 5 => ⟨((375365633616861/1125899906842624), (338000610591571/1125899906842624)), (431633/140737488355328), by norm_num⟩
  | 6 => ⟨((189394783520759/9007199254740992), (450746332197095/2251799813685248)), (35005589/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-215163547/134217728), (-8039585933/268435456)), (1/134217728), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-110690087/67108864), (-2067967553/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89233899065819/562949953421312), (489233525353189/4503599627370496)), (2718235/562949953421312), by norm_num⟩
  | 1 => ⟨((-898335935/2147483648), (-1231303521/4294967296)), (111/8589934592), by norm_num⟩
  | 2 => ⟨((4741520067/8589934592), (1624740291/4294967296)), (149/8589934592), by norm_num⟩
  | 3 => ⟨((-2085523881/4294967296), (-2858521849/8589934592)), (133/8589934592), by norm_num⟩
  | 4 => ⟨((1375954271/4294967296), (1885950759/8589934592)), (89/8589934592), by norm_num⟩
  | 5 => ⟨((-2904977763/17179869184), (-1990852869/17179869184)), (3/536870912), by norm_num⟩
  | 6 => ⟨((2555467619/34359738368), (218915619/4294967296)), (43/17179869184), by norm_num⟩
  | 7 => ⟨((-1926864443/68719476736), (-330131925/17179869184)), (33/34359738368), by norm_num⟩
  | 8 => ⟨((5085105731/549755813888), (3484948305/549755813888)), (177/549755813888), by norm_num⟩
  | 9 => ⟨((-2982196789/1099511627776), (-1021886485/549755813888)), (53/549755813888), by norm_num⟩
  | 10 => ⟨((3148075317/4398046511104), (1078726807/2199023255552)), (57/2199023255552), by norm_num⟩
  | 11 => ⟨((-1510536589/8796093022208), (-2070415917/17592186044416)), (111/17592186044416), by norm_num⟩
  | 12 => ⟨((83049847/2199023255552), (910657717/35184372088832)), (25/17592186044416), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581827225343001/10141204801825835211973625643008), (48913774553/633825300114114700748351602688)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1779424346235611/633825300114114700748351602688), (231710125147/158456325028528675187087900672)), (11537/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890479277633975/39614081257132168796771975168), (1042543809333/39614081257132168796771975168)), (25959/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945150163855069/1237940039285380274899124224), (1107516392347/2475880078570760549798248448)), (431/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((885983225350327/77371252455336267181195264), (553653371393/77371252455336267181195264)), (27585/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550280569069747/9671406556917033397649408), (1037877372435/9671406556917033397649408)), (25863/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259424799962273/604462909807314587353088), (453960031203/302231454903657293676544)), (2829/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888825482079427/75557863725914323419136), (1474952782689/75557863725914323419136)), (36781/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81144644397033/295147905179352825856), (1105849561511/4722366482869645213696)), (27589/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622513183875163/590295810358705651712), (1519950221241/590295810358705651712)), (9485/147573952589676412928), by norm_num⟩
  | 8 => ⟨((28512584617461/1152921504606846976), (474762202169/18446744073709551616)), (47433/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228019160640077/1152921504606846976), (1067604131255/4611686018427387904)), (26687/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595400842052855/1152921504606846976), (266710278525/144115188075855872)), (13347/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195817804225475/144115188075855872), (932628284557/72057594037927936)), (23365/72057594037927936), by norm_num⟩
  | 4 => ⟨((373372707718943/9007199254740992), (1397228804825/18014398509481984)), (35063/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491570739525389/9007199254740992), (3487082240285/9007199254740992)), (87713/9007199254740992), by norm_num⟩
  | 2 => ⟨((279070379055177/562949953421312), (6956226745215/4503599627370496)), (175591/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222998305845707/2251799813685248), (5194803062401/1125899906842624)), (131901/1125899906842624), by norm_num⟩
  | 0 => ⟨((274301383655991/281474976710656), (20600936875589/2251799813685248)), (264639/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((274301383655991/281474976710656), (20600936875589/2251799813685248)), (1009517673972701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2138296447568103/2251799813685248), (10037953560953/562949953421312)), (1041263/2251799813685248), by norm_num⟩
  | 2 => ⟨((2029798342515621/2251799813685248), (19063968572865/562949953421312)), (1007345/1125899906842624), by norm_num⟩
  | 3 => ⟨((1827101293778813/2251799813685248), (137475850475863/2251799813685248)), (3768583/2251799813685248), by norm_num⟩
  | 4 => ⟨((1474109513683497/2251799813685248), (223094702061203/2251799813685248)), (6575783/2251799813685248), by norm_num⟩
  | 5 => ⟨((942902472653459/2251799813685248), (292091704388757/2251799813685248)), (9912469/2251799813685248), by norm_num⟩
  | 6 => ⟨((89233899065819/562949953421312), (489233525353189/4503599627370496)), (2718235/562949953421312), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-110690087/67108864), (-2067967553/67108864)), (1/67108864), by norm_num⟩, -5, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-56791929/33554432), (-4244060851/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((405790016380145/2251799813685248), (-168567347344005/4503599627370496)), (30724395/9007199254740992), by norm_num⟩
  | 1 => ⟨((-523996227/1073741824), (870683363/8589934592)), (81/8589934592), by norm_num⟩
  | 2 => ⟨((177376011/268435456), (-147365891/1073741824)), (7/536870912), by norm_num⟩
  | 3 => ⟨((-640457523/1073741824), (1064197949/8589934592)), (103/8589934592), by norm_num⟩
  | 4 => ⟨((433597781/1073741824), (-1440950735/17179869184)), (141/17179869184), by norm_num⟩
  | 5 => ⟨((-1878727293/8589934592), (390216693/8589934592)), (39/8589934592), by norm_num⟩
  | 6 => ⟨((6783583765/68719476736), (-1408968525/68719476736)), (143/68719476736), by norm_num⟩
  | 7 => ⟨((-2624326483/68719476736), (1090159285/137438953472)), (113/137438953472), by norm_num⟩
  | 8 => ⟨((1776701965/137438953472), (-369025759/137438953472)), (39/137438953472), by norm_num⟩
  | 9 => ⟨((-4276798323/1099511627776), (111037809/137438953472)), (3/34359738368), by norm_num⟩
  | 10 => ⟨((144772307/137438953472), (-962227075/4398046511104)), (53/2199023255552), by norm_num⟩
  | 11 => ⟨((-4562044219/17592186044416), (947548809/17592186044416)), (53/8796093022208), by norm_num⟩
  | 12 => ⟨((1029520397/17592186044416), (-855336581/70368744177664)), (97/70368744177664), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581771056014629/10141204801825835211973625643008), (-133381501399/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444839558576931/158456325028528675187087900672), (-78974805151/158456325028528675187087900672)), (23059/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890404936133865/39614081257132168796771975168), (-355333683537/39614081257132168796771975168)), (25941/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890221383298923/2475880078570760549798248448), (-377476856521/2475880078570760549798248448)), (27563/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885943777562865/77371252455336267181195264), (-188701773981/77371252455336267181195264)), (6891/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775103328167351/4835703278458516698824704), (-11054311123/302231454903657293676544)), (12921/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629680089080335/302231454903657293676544), (-154721431871/302231454903657293676544)), (22613/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888720568801895/75557863725914323419136), (-502698737097/75557863725914323419136)), (18373/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298235710347865/4722366482869645213696), (-188448211919/2361183241434822606848)), (27561/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811202623409587/295147905179352825856), (-518025275525/590295810358705651712)), (18949/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824670700950031/73786976294838206464), (-647220790679/73786976294838206464)), (47375/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456000503808953/2305843009213693952), (-727696289617/9223372036854775808)), (53301/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595249926751285/1152921504606846976), (-727162797329/1152921504606846976)), (53305/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195686151664115/144115188075855872), (-317833897237/72057594037927936)), (5831/18014398509481984), by norm_num⟩
  | 4 => ⟨((1493294147244059/36028797018963968), (-952303698175/36028797018963968)), (34991/18014398509481984), by norm_num⟩
  | 3 => ⟨((745663136679183/4503599627370496), (-297071521121/2251799813685248)), (10937/1125899906842624), by norm_num⟩
  | 2 => ⟨((2232078252268947/4503599627370496), (-2370303338945/4503599627370496)), (87525/2251799813685248), by norm_num⟩
  | 1 => ⟨((2222281470758737/2251799813685248), (-3539824102685/2251799813685248)), (4105/35184372088832), by norm_num⟩
  | 0 => ⟨((2193018469283775/2251799813685248), (-7017370983181/2251799813685248)), (526029/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2193018469283775/2251799813685248), (-7017370983181/2251799813685248)), (2006641396529387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((533937423510737/562949953421312), (-6834188402719/1125899906842624)), (1027875/2251799813685248), by norm_num⟩
  | 2 => ⟨((1012798718464947/1125899906842624), (-25927910112491/2251799813685248)), (1962283/2251799813685248), by norm_num⟩
  | 3 => ⟨((910909729861887/1125899906842624), (-11661673464405/562949953421312)), (3575517/2251799813685248), by norm_num⟩
  | 4 => ⟨((736488698867083/1125899906842624), (-37739524661613/1125899906842624)), (1483421/562949953421312), by norm_num⟩
  | 5 => ⟨((1921987304730679/4503599627370496), (-98746729598153/2251799813685248)), (8160629/2251799813685248), by norm_num⟩
  | 6 => ⟨((405790016380145/2251799813685248), (-168567347344005/4503599627370496)), (30724395/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56791929/33554432), (-4244060851/134217728)), (1/67108864), by norm_num⟩, -5, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile027Terms1
