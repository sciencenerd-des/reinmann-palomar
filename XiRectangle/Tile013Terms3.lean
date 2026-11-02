/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile013Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨13,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3807/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3807/640))
  have he : value ((3/4), (3807/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-4978472343/2147483648), (-78971017539/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((198365871454457/2251799813685248), (395775553519893/9007199254740992)), (638331/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1169504795/4294967296), (-37333955015/274877906944)), (31/137438953472), by norm_num⟩
  | 2 => ⟨((14459955883/34359738368), (3606276247/17179869184)), (25/68719476736), by norm_num⟩
  | 3 => ⟨((-29797558339/68719476736), (-29725741275/137438953472)), (27/68719476736), by norm_num⟩
  | 4 => ⟨((11513189729/34359738368), (5742720515/34359738368)), (43/137438953472), by norm_num⟩
  | 5 => ⟨((-28470206581/137438953472), (-28401588655/274877906944)), (55/274877906944), by norm_num⟩
  | 6 => ⟨((58668411465/549755813888), (29263505425/549755813888)), (29/274877906944), by norm_num⟩
  | 7 => ⟨((-25906650073/549755813888), (-3230526343/137438953472)), (53/1099511627776), by norm_num⟩
  | 8 => ⟨((1251227425/68719476736), (9985694073/1099511627776)), (21/1099511627776), by norm_num⟩
  | 9 => ⟨((-55005825273/8796093022208), (-13718313025/4398046511104)), (59/8796093022208), by norm_num⟩
  | 10 => ⟨((8501267055/4398046511104), (33923110359/35184372088832)), (75/35184372088832), by norm_num⟩
  | 11 => ⟨((-76444443271/140737488355328), (-19065049867/70368744177664)), (43/70368744177664), by norm_num⟩
  | 12 => ⟨((78764339825/562949953421312), (39287252343/562949953421312)), (45/281474976710656), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085591/5070602400912917605986812821504), (602696367841/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778393265027377/633825300114114700748351602688), (712972991411/633825300114114700748351602688)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889319523677381/39614081257132168796771975168), (801933200487/39614081257132168796771975168)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944534176149531/1237940039285380274899124224), (851852602771/2475880078570760549798248448)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221341846406233/19342813113834066795298816), (425813049437/77371252455336267181195264)), (431/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193640772993469/1208925819614629174706176), (798158891449/9671406556917033397649408)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314603756809279/151115727451828646838272), (174537137117/151115727451828646838272)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887185190405855/75557863725914323419136), (567020344743/37778931862957161709568)), (575/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648542303375179/2361183241434822606848), (850136354091/4722366482869645213696)), (863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405205794530475/147573952589676412928), (1168297348669/590295810358705651712)), (593/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227836770329257/9223372036854775808), (1459412137325/73786976294838206464)), (741/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821779849096327/9223372036854775808), (1640520345003/9223372036854775808)), (417/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593029558560753/1152921504606846976), (1638874061271/1152921504606846976)), (1669/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596872675144585/72057594037927936), (1432164936363/144115188075855872)), (1461/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490386982017817/36028797018963968), (2094290203/35184372088832)), (2191/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487699370620067/9007199254740992), (1337119448215/4503599627370496)), (685/2251799813685248), by norm_num⟩
  | 2 => ⟨((1112422782782187/2251799813685248), (5329169409117/4503599627370496)), (2741/2251799813685248), by norm_num⟩
  | 1 => ⟨((138217818048635/140737488355328), (124150863957/35184372088832)), (4117/1125899906842624), by norm_num⟩
  | 0 => ⟨((2171635406792413/2251799813685248), (15699944676619/2251799813685248)), (16507/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2171635406792413/2251799813685248), (15699944676619/2251799813685248)), (62969216353606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2094215401880639/2251799813685248), (3785256080183/281474976710656)), (16035/1125899906842624), by norm_num⟩
  | 2 => ⟨((486812939626731/562949953421312), (56325728672715/2251799813685248)), (60515/2251799813685248), by norm_num⟩
  | 3 => ⟨((420620962870743/562949953421312), (97415741435405/2251799813685248)), (53845/1125899906842624), by norm_num⟩
  | 4 => ⟨((313223012396065/562949953421312), (145572808780967/2251799813685248)), (170245/2251799813685248), by norm_num⟩
  | 5 => ⟨((171923258435743/562949953421312), (161992210540983/2251799813685248)), (422919/4503599627370496), by norm_num⟩
  | 6 => ⟨((198365871454457/2251799813685248), (395775553519893/9007199254740992)), (638331/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4978472343/2147483648), (-78971017539/4294967296)), (1/2147483648), by norm_num⟩, -3, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2525033459/1073741824), (-20026671621/1073741824)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((840817173967565/9007199254740992), (168923452320705/9007199254740992)), (998237/18014398509481984), by norm_num⟩
  | 1 => ⟨((-80455852833/274877906944), (-2020486861/34359738368)), (49/274877906944), by norm_num⟩
  | 2 => ⟨((63067215299/137438953472), (3167612433/34359738368)), (5/17179869184), by norm_num⟩
  | 3 => ⟨((-65915629595/137438953472), (-13242707283/137438953472)), (43/137438953472), by norm_num⟩
  | 4 => ⟨((25834759417/68719476736), (20761216045/274877906944)), (35/137438953472), by norm_num⟩
  | 5 => ⟨((-32401895489/137438953472), (-13019334565/274877906944)), (45/274877906944), by norm_num⟩
  | 6 => ⟨((67730637261/549755813888), (425229669/17179869184)), (49/549755813888), by norm_num⟩
  | 7 => ⟨((-30338431625/549755813888), (-12190218675/1099511627776)), (23/549755813888), by norm_num⟩
  | 8 => ⟨((95125976881/4398046511104), (19111180073/4398046511104)), (37/2199023255552), by norm_num⟩
  | 9 => ⟨((-33140772255/4398046511104), (-13316221017/8796093022208)), (53/8796093022208), by norm_num⟩
  | 10 => ⟨((41565079887/17592186044416), (16701173591/35184372088832)), (17/8796093022208), by norm_num⟩
  | 11 => ⟨((-47391660935/70368744177664), (-19042339343/140737488355328)), (5/8796093022208), by norm_num⟩
  | 12 => ⟨((49532092915/281474976710656), (19902381623/562949953421312)), (43/281474976710656), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316641/5070602400912917605986812821504), (258261708155/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778342115192955/633825300114114700748351602688), (305499580057/633825300114114700748351602688)), (721/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944631002102057/19807040628566084398385987584), (343616966649/39614081257132168796771975168)), (811/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889007268793807/2475880078570760549798248448), (365005486041/2475880078570760549798248448)), (431/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770673722521255/154742504910672534362390528), (364907045919/154742504910672534362390528)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549068987694853/9671406556917033397649408), (341995800419/9671406556917033397649408)), (101/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629182508711733/302231454903657293676544), (149570906219/302231454903657293676544)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887103993612635/75557863725914323419136), (485909573109/75557863725914323419136)), (1149/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162127971202167/590295810358705651712), (182130440665/2361183241434822606848)), (431/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620739625224977/590295810358705651712), (500580519639/590295810358705651712)), (593/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822589868597729/73786976294838206464), (312654327423/36893488147419103232)), (1481/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455415680073203/2305843009213693952), (702899345669/9223372036854775808)), (1667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((12444630327035/9007199254740992), (702183946235/1152921504606846976)), (1667/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596821683134769/72057594037927936), (153401777437/36028797018963968)), (1459/144115188075855872), by norm_num⟩
  | 4 => ⟨((745117285434643/18014398509481984), (7178167405/281474976710656)), (547/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487509842295387/9007199254740992), (143212890395/1125899906842624)), (2735/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224469454056973/4503599627370496), (570754306925/1125899906842624)), (5471/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210928243594767/2251799813685248), (3403629976607/2251799813685248)), (8211/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170550761200119/2251799813685248), (6724134983751/2251799813685248)), (2055/281474976710656), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2170550761200119/2251799813685248), (6724134983751/2251799813685248)), (7839203954601199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1046106621983597/1125899906842624), (12963031810103/2251799813685248)), (31793/2251799813685248), by norm_num⟩
  | 2 => ⟨((485965514278377/562949953421312), (24088666026381/2251799813685248)), (59447/2251799813685248), by norm_num⟩
  | 3 => ⟨((1677777664912229/2251799813685248), (41588993489193/2251799813685248)), (25977/562949953421312), by norm_num⟩
  | 4 => ⟨((624657714109775/1125899906842624), (15493625134499/562949953421312)), (158679/2251799813685248), by norm_num⟩
  | 5 => ⟨((691423896124405/2251799813685248), (34383917792233/1125899906842624)), (369615/4503599627370496), by norm_num⟩
  | 6 => ⟨((840817173967565/9007199254740992), (168923452320705/9007199254740992)), (998237/18014398509481984), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2525033459/1073741824), (-20026671621/1073741824)), (1/2147483648), by norm_num⟩, -3, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-5118613975/2147483648), (-2537312943/134217728)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((51838995228665/562949953421312), (-45580061786671/9007199254740992)), (847767/18014398509481984), by norm_num⟩
  | 1 => ⟨((-10055366049/34359738368), (2210325469/137438953472)), (43/274877906944), by norm_num⟩
  | 2 => ⟨((63912989175/137438953472), (-7024533323/274877906944)), (35/137438953472), by norm_num⟩
  | 3 => ⟨((-67706306685/137438953472), (930181043/34359738368)), (39/137438953472), by norm_num⟩
  | 4 => ⟨((107587143649/274877906944), (-5912330853/274877906944)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((-34191773397/137438953472), (3757941143/274877906944)), (21/137438953472), by norm_num⟩
  | 6 => ⟨((72442197607/549755813888), (-995244937/137438953472)), (23/274877906944), by norm_num⟩
  | 7 => ⟨((-65778629595/1099511627776), (3614790839/1099511627776)), (43/1099511627776), by norm_num⟩
  | 8 => ⟨((52262006435/2199023255552), (-89749999/68719476736)), (35/2199023255552), by norm_num⟩
  | 9 => ⟨((-4613651937/549755813888), (4056609111/8796093022208)), (51/8796093022208), by norm_num⟩
  | 10 => ⟨((46919789473/17592186044416), (-5156848849/35184372088832)), (67/35184372088832), by norm_num⟩
  | 11 => ⟨((-108446266657/140737488355328), (5959542995/140737488355328)), (79/140737488355328), by norm_num⟩
  | 12 => ⟨((114882691045/562949953421312), (-6313249481/562949953421312)), (43/281474976710656), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790435469823053/5070602400912917605986812821504), (-17877908497/2535301200456458802993406410752)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778292978584597/633825300114114700748351602688), (-10573394189/79228162514264337593543950336)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472301684859397/9903520314283042199192993792), (-95140902871/39614081257132168796771975168)), (811/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888948567556453/2475880078570760549798248448), (-12632830333/309485009821345068724781056)), (431/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770615041047121/154742504910672534362390528), (-101035017667/154742504910672534362390528)), (431/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549013994802231/9671406556917033397649408), (-94690988193/9671406556917033397649408)), (101/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629158459810811/302231454903657293676544), (-82825285829/604462909807314587353088)), (707/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887025873999021/75557863725914323419136), (-134536123447/75557863725914323419136)), (1149/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648482607142803/2361183241434822606848), (-50427011425/2361183241434822606848)), (431/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810329583734201/295147905179352825856), (-138596215951/590295810358705651712)), (1185/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911244690034029/36893488147419103232), (-173128255417/73786976294838206464)), (1481/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910774892811421/4611686018427387904), (-194608528247/9223372036854775808)), (833/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796399945337861/576460752303423488), (-194407782987/1152921504606846976)), (833/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193544835167305/144115188075855872), (-169881251345/144115188075855872)), (729/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490087095994631/36028797018963968), (-63592864415/9007199254740992)), (1093/18014398509481984), by norm_num⟩
  | 3 => ⟨((743663030244715/4503599627370496), (-158588828255/4503599627370496)), (2733/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224103570518319/4503599627370496), (-632001576615/4503599627370496)), (5465/4503599627370496), by norm_num⟩
  | 1 => ⟨((69074487500485/70368744177664), (-58883742299/140737488355328)), (8199/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169478090680643/2251799813685248), (-1860960454285/2251799813685248)), (16403/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2169478090680643/2251799813685248), (-1860960454285/2251799813685248)), (62572487837981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2090164362819953/2251799813685248), (-3585854220839/2251799813685248)), (31635/2251799813685248), by norm_num⟩
  | 2 => ⟨((1940125484823717/2251799813685248), (-6656919196027/2251799813685248)), (29415/1125899906842624), by norm_num⟩
  | 3 => ⟨((417892674052709/562949953421312), (-5735526978967/1125899906842624)), (101723/2251799813685248), by norm_num⟩
  | 4 => ⟨((620396402551265/1125899906842624), (-8515267447045/1125899906842624)), (38015/562949953421312), by norm_num⟩
  | 5 => ⟨((1367152387810423/4503599627370496), (-18768422517143/2251799813685248)), (339755/4503599627370496), by norm_num⟩
  | 6 => ⟨((51838995228665/562949953421312), (-45580061786671/9007199254740992)), (847767/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5118613975/2147483648), (-2537312943/134217728)), (1/2147483648), by norm_num⟩, -3, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-5184362399/2147483648), (-82236948557/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1540371326781495/18014398509481984), (-472656963583339/18014398509481984)), (510699/9007199254740992), by norm_num⟩
  | 1 => ⟨((-75657104875/274877906944), (23215089013/274877906944)), (13/68719476736), by norm_num⟩
  | 2 => ⟨((30441353233/68719476736), (-18681622199/137438953472)), (11/34359738368), by norm_num⟩
  | 3 => ⟨((-65324623999/137438953472), (20044607355/137438953472)), (49/137438953472), by norm_num⟩
  | 4 => ⟨((6570995405/17179869184), (-32260551017/274877906944)), (81/274877906944), by norm_num⟩
  | 5 => ⟨((-67683898415/274877906944), (20768541553/274877906944)), (27/137438953472), by norm_num⟩
  | 6 => ⟨((72622021447/549755813888), (-22283785441/549755813888)), (15/137438953472), by norm_num⟩
  | 7 => ⟨((-33394467027/549755813888), (5123481303/274877906944)), (57/1099511627776), by norm_num⟩
  | 8 => ⟨((53746321299/2199023255552), (-16491850105/2199023255552)), (47/2199023255552), by norm_num⟩
  | 9 => ⟨((-9611263017/1099511627776), (23593430049/8796093022208)), (69/8796093022208), by norm_num⟩
  | 10 => ⟨((49499939475/17592186044416), (-7594432161/8796093022208)), (91/35184372088832), by norm_num⟩
  | 11 => ⟨((-57939694003/70368744177664), (17778570245/70368744177664)), (55/70368744177664), by norm_num⟩
  | 12 => ⟨((31083446721/140737488355328), (-4768917497/70368744177664)), (61/281474976710656), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058242031/10141204801825835211973625643008), (-387821021663/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778245697347427/633825300114114700748351602688), (-229354414441/316912650057057350374175801344)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889153553030539/39614081257132168796771975168), (-64492447097/4951760157141521099596496896)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944446031397767/1237940039285380274899124224), (-68506358199/309485009821345068724781056)), (431/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885279271404861/77371252455336267181195264), (-547899133109/154742504910672534362390528)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548961034636923/9671406556917033397649408), (-513494280699/9671406556917033397649408)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258270586410379/604462909807314587353088), (-224573202809/302231454903657293676544)), (707/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886950595533313/75557863725914323419136), (-91195125855/9444732965739290427392)), (1149/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296908766815995/4722366482869645213696), (-273453365999/2361183241434822606848)), (431/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620581570694187/590295810358705651712), (-375783991907/295147905179352825856)), (1185/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822392411852959/73786976294838206464), (-938817283999/73786976294838206464)), (1481/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227680091819199/1152921504606846976), (-1055286489993/9223372036854775808)), (1667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592690887341535/1152921504606846976), (-527091962023/576460752303423488)), (417/288230376151711744), by norm_num⟩
  | 5 => ⟨((298362377744505/36028797018963968), (-230293023745/36028797018963968)), (1459/144115188075855872), by norm_num⟩
  | 4 => ⟨((372486054308003/9007199254740992), (-689642165213/18014398509481984)), (2189/36028797018963968), by norm_num⟩
  | 3 => ⟨((92946728146481/562949953421312), (-859892461991/4503599627370496)), (2737/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223747315724885/4503599627370496), (-3426643037013/4503599627370496)), (1369/1125899906842624), by norm_num⟩
  | 1 => ⟨((2209850633559417/2251799813685248), (-2553884251001/1125899906842624)), (8219/2251799813685248), by norm_num⟩
  | 0 => ⟨((2168417832439399/2251799813685248), (-315233626779/70368744177664)), (16465/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2168417832439399/2251799813685248), (-315233626779/70368744177664)), (62808999068450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2088078216496917/2251799813685248), (-19427893042011/2251799813685248)), (31859/2251799813685248), by norm_num⟩
  | 2 => ⟨((968046353118289/1125899906842624), (-1125959332811/70368744177664)), (14909/562949953421312), by norm_num⟩
  | 3 => ⟨((208008985363843/281474976710656), (-61958236636155/2251799813685248)), (104459/2251799813685248), by norm_num⟩
  | 4 => ⟨((614019148505351/1125899906842624), (-91573823635965/2251799813685248)), (160139/2251799813685248), by norm_num⟩
  | 5 => ⟨((665997165749503/2251799813685248), (-199762273262871/4503599627370496)), (375383/4503599627370496), by norm_num⟩
  | 6 => ⟨((1540371326781495/18014398509481984), (-472656963583339/18014398509481984)), (510699/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5184362399/2147483648), (-82236948557/4294967296)), (1/2147483648), by norm_num⟩, -3, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-5247531779/2147483648), (-5202435803/268435456)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1349092202277551/18014398509481984), (-792319635210291/18014398509481984)), (148211/2251799813685248), by norm_num⟩
  | 1 => ⟨((-16767397437/68719476736), (9847464983/68719476736)), (61/274877906944), by norm_num⟩
  | 2 => ⟨((54629799541/137438953472), (-32083991569/137438953472)), (51/137438953472), by norm_num⟩
  | 3 => ⟨((-14832430063/34359738368), (17422123643/68719476736)), (29/68719476736), by norm_num⟩
  | 4 => ⟨((48325489039/137438953472), (-28381480363/137438953472)), (49/137438953472), by norm_num⟩
  | 5 => ⟨((-31489821707/137438953472), (18493920583/137438953472)), (33/137438953472), by norm_num⟩
  | 6 => ⟨((68397919391/549755813888), (-40169985751/549755813888)), (37/274877906944), by norm_num⟩
  | 7 => ⟨((-63670578393/1099511627776), (37393626145/1099511627776)), (35/549755813888), by norm_num⟩
  | 8 => ⟨((51861222759/2199023255552), (-7614502743/549755813888)), (59/2199023255552), by norm_num⟩
  | 9 => ⟨((-37548637851/4398046511104), (5513063339/1099511627776)), (11/1099511627776), by norm_num⟩
  | 10 => ⟨((12233708699/4398046511104), (-14369674063/8796093022208)), (59/17592186044416), by norm_num⟩
  | 11 => ⟨((-28988075607/35184372088832), (8512324603/17592186044416)), (9/8796093022208), by norm_num⟩
  | 12 => ⟨((62963965853/281474976710656), (-36978633759/281474976710656)), (5/17592186044416), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((6174971645405/39614081257132168796771975168), (-691722873683/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((222275016462823/79228162514264337593543950336), (-409059797143/316912650057057350374175801344)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944551144396129/19807040628566084398385987584), (-460094921035/19807040628566084398385987584)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236104698739087/309485009821345068724781056), (-488729052763/1237940039285380274899124224)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770504064733283/154742504910672534362390528), (-244296044549/38685626227668133590597632)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387227488983079/2417851639229258349412352), (-915819226251/9671406556917033397649408)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258225887047455/604462909807314587353088), (-400525501281/302231454903657293676544)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943438974393677/37778931862957161709568), (-40661338957/2361183241434822606848)), (575/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296854272784971/4722366482869645213696), (-975395487083/4722366482869645213696)), (863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810253313434323/295147905179352825856), (-167549340107/73786976294838206464)), (593/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822298710351915/73786976294838206464), (-1674333127783/73786976294838206464)), (1483/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227666911328909/1152921504606846976), (-1882030752883/9223372036854775808)), (417/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796292703223515/576460752303423488), (-1880040270955/1152921504606846976)), (1669/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149169646733627/18014398509481984), (-410699685979/36028797018963968)), (1461/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489805629582715/36028797018963968), (-307466514705/4503599627370496)), (137/2251799813685248), by norm_num⟩
  | 3 => ⟨((371743568450693/2251799813685248), (-3066865347601/9007199254740992)), (2741/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111700071332899/2251799813685248), (-6110393957981/4503599627370496)), (5485/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209328844788369/2251799813685248), (-4553733914935/1125899906842624)), (8239/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167370261921445/2251799813685248), (-17983751034663/2251799813685248)), (16525/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2167370261921445/2251799813685248), (-17983751034663/2251799813685248)), (63037880904387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2085962707880709/2251799813685248), (-17309463724725/1125899906842624)), (8019/562949953421312), by norm_num⟩
  | 2 => ⟨((965903345868939/1125899906842624), (-16034682836259/562949953421312)), (60415/2251799813685248), by norm_num⟩
  | 3 => ⟨((1655459466125417/2251799813685248), (-55024265327183/1125899906842624)), (53551/1125899906842624), by norm_num⟩
  | 4 => ⟨((151458588164847/281474976710656), (-40452281925277/562949953421312)), (83973/1125899906842624), by norm_num⟩
  | 5 => ⟨((320179184863153/1125899906842624), (-43533855691527/562949953421312)), (409753/4503599627370496), by norm_num⟩
  | 6 => ⟨((1349092202277551/18014398509481984), (-792319635210291/18014398509481984)), (148211/2251799813685248), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5247531779/2147483648), (-5202435803/268435456)), (1/2147483648), by norm_num⟩, -3, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-165884901/67108864), (-84203175751/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((276768186946741/4503599627370496), (-1042826517301705/18014398509481984)), (667981/9007199254740992), by norm_num⟩
  | 1 => ⟨((-55675219353/274877906944), (26222122807/137438953472)), (69/274877906944), by norm_num⟩
  | 2 => ⟨((45874110117/137438953472), (-21605959763/68719476736)), (59/137438953472), by norm_num⟩
  | 3 => ⟨((-25198930553/68719476736), (2967071613/8589934592)), (67/137438953472), by norm_num⟩
  | 4 => ⟨((20762891075/68719476736), (-39115936025/137438953472)), (57/137438953472), by norm_num⟩
  | 5 => ⟨((-6843110185/34359738368), (50359275/268435456)), (77/274877906944), by norm_num⟩
  | 6 => ⟨((3758962471/34359738368), (-14163281501/137438953472)), (87/549755813888), by norm_num⟩
  | 7 => ⟨((-14158773817/274877906944), (53348417503/1099511627776)), (21/274877906944), by norm_num⟩
  | 8 => ⟨((11666252181/549755813888), (-1373653759/68719476736)), (71/2199023255552), by norm_num⟩
  | 9 => ⟨((-17088917345/2199023255552), (64388817067/8796093022208)), (53/4398046511104), by norm_num⟩
  | 10 => ⟨((45057827029/17592186044416), (-21221503705/8796093022208)), (9/2199023255552), by norm_num⟩
  | 11 => ⟨((-27000590441/35184372088832), (12716838957/17592186044416)), (11/8796093022208), by norm_num⟩
  | 12 => ⟨((7415795115/35184372088832), (-55883502205/281474976710656)), (49/140737488355328), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (-246038489005/2535301200456458802993406410752)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778156157273765/633825300114114700748351602688), (-581965719817/316912650057057350374175801344)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944526403855889/19807040628566084398385987584), (-327285644187/9903520314283042199192993792)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888785002377727/2475880078570760549798248448), (-347653344863/618970019642690137449562112)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770451461601689/154742504910672534362390528), (-695109561245/77371252455336267181195264)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548860623943793/9671406556917033397649408), (-1302911682665/9671406556917033397649408)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629091352512987/302231454903657293676544), (-569814575121/302231454903657293676544)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943403873525355/37778931862957161709568), (-1851112913033/75557863725914323419136)), (1151/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296801594444545/4722366482869645213696), (-1387648652043/4722366482869645213696)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((810217075148931/295147905179352825856), (-119181423743/36893488147419103232)), (1187/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822208049006141/73786976294838206464), (-2381958500437/73786976294838206464)), (371/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227654150826377/1152921504606846976), (-334676130945/1152921504606846976)), (835/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592483210275587/1152921504606846976), (-2674544137161/1152921504606846976)), (835/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193267626538357/144115188075855872), (-584251777085/36028797018963968)), (1463/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489671058446221/36028797018963968), (-3499082657293/36028797018963968)), (1097/18014398509481984), by norm_num⟩
  | 3 => ⟨((23231337888677/140737488355328), (-1090656704285/2251799813685248)), (2745/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223061550708173/4503599627370496), (-8691663958949/4503599627370496)), (5495/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208817759634553/2251799813685248), (-12953835372749/2251799813685248)), (8259/2251799813685248), by norm_num⟩
  | 0 => ⟨((2166335529604795/2251799813685248), (-12787451874357/1125899906842624)), (16583/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2166335529604795/2251799813685248), (-12787451874357/1125899906842624)), (63259133345793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((130239029314703/140737488355328), (-49208479652895/2251799813685248)), (32285/2251799813685248), by norm_num⟩
  | 2 => ⟨((963652034453651/1125899906842624), (-45537722030853/1125899906842624)), (30583/1125899906842624), by norm_num⟩
  | 3 => ⟨((1645886199559679/2251799813685248), (-77951011831019/1125899906842624)), (27413/562949953421312), by norm_num⟩
  | 4 => ⟨((298054463434459/562949953421312), (-227903908393023/2251799813685248)), (87739/1125899906842624), by norm_num⟩
  | 5 => ⟨((304077478599049/1125899906842624), (-482655885965489/4503599627370496)), (442669/4503599627370496), by norm_num⟩
  | 6 => ⟨((276768186946741/4503599627370496), (-1042826517301705/18014398509481984)), (667981/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-84203175751/4294967296)), (1/2147483648), by norm_num⟩, -3, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile013Terms3
