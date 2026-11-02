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
namespace Reinmann.XiRectangle.Tile011Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨11,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3243/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3243/640))
  have he : value ((3/4), (3243/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4978472343/2147483648), (-33635803767/2147483648)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-885791455762361/9007199254740992), (-39951082445189/9007199254740992)), (141991/1125899906842624), by norm_num⟩
  | 1 => ⟨((83557708575/274877906944), (1884315367/137438953472)), (109/274877906944), by norm_num⟩
  | 2 => ⟨((-4035631633/8589934592), (-5824498795/274877906944)), (171/274877906944), by norm_num⟩
  | 3 => ⟨((16632411605/34359738368), (3000628841/137438953472)), (89/137438953472), by norm_num⟩
  | 4 => ⟨((-51411490373/137438953472), (-4637535567/274877906944)), (139/274877906944), by norm_num⟩
  | 5 => ⟨((127132079467/549755813888), (5733927727/549755813888)), (87/274877906944), by norm_num⟩
  | 6 => ⟨((-4093444321/34359738368), (-2953969005/549755813888)), (91/549755813888), by norm_num⟩
  | 7 => ⟨((115684664473/2199023255552), (5217624915/2199023255552)), (163/2199023255552), by norm_num⟩
  | 8 => ⟨((-5587284517/274877906944), (-4031975029/4398046511104)), (1/34359738368), by norm_num⟩
  | 9 => ⟨((61406341835/8796093022208), (5539113771/17592186044416)), (89/8796093022208), by norm_num⟩
  | 10 => ⟨((-75923843807/35184372088832), (-856081791/8796093022208)), (111/35184372088832), by norm_num⟩
  | 11 => ⟨((10667446565/17592186044416), (962249149/35184372088832)), (63/70368744177664), by norm_num⟩
  | 12 => ⟨((-43964706935/281474976710656), (-495725495/70368744177664)), (33/140737488355328), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085591/5070602400912917605986812821504), (-2016782209339/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889190670033323/316912650057057350374175801344), (-596449274271/79228162514264337593543950336)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944652721889477/19807040628566084398385987584), (-5366927134025/39614081257132168796771975168)), (51/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944526258610057/1237940039285380274899124224), (-5701007870827/2475880078570760549798248448)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770717952457855/154742504910672534362390528), (-5699486693363/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549109371880433/9671406556917033397649408), (-5341652761457/9671406556917033397649408)), (407/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314599818266655/151115727451828646838272), (-4672330419103/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943578817443699/37778931862957161709568), (-7589507971691/75557863725914323419136)), (579/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648531115636687/2361183241434822606848), (-177796287703/147573952589676412928)), (869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620789638313205/590295810358705651712), (-7818731843599/590295810358705651712)), (1195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455662020852981/18446744073709551616), (-305217482717/2305843009213693952)), (1495/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910861153526905/4611686018427387904), (-2744739074241/2305843009213693952)), (1683/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398241225514311/288230376151711744), (-5483934753673/576460752303423488)), (843/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193680791563191/144115188075855872), (-599026216573/9007199254740992)), (739/72057594037927936), by norm_num⟩
  | 4 => ⟨((745137111999163/18014398509481984), (-896982014953/2251799813685248)), (2221/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487530672471735/9007199254740992), (-17896071160057/9007199254740992)), (2785/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112212676741431/2251799813685248), (-17830788784969/2251799813685248)), (1399/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105324626655877/1125899906842624), (-6645807013943/281474976710656)), (4231/1125899906842624), by norm_num⟩
  | 0 => ⟨((542287691428577/562949953421312), (-52516149654965/1125899906842624)), (4297/562949953421312), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((542287691428577/562949953421312), (-52516149654965/1125899906842624)), (16391756297874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1042318067523559/1125899906842624), (-101177241017711/1125899906842624)), (1085/70368744177664), by norm_num⟩
  | 2 => ⟨((477924419944249/562949953421312), (-93666289244739/562949953421312)), (35263/1125899906842624), by norm_num⟩
  | 3 => ⟨((390156133957063/562949953421312), (-636154694513239/2251799813685248)), (71609/1125899906842624), by norm_num⟩
  | 4 => ⟨((112735162676065/281474976710656), (-881782313690571/2251799813685248)), (139719/1125899906842624), by norm_num⟩
  | 5 => ⟨((15920524051451/2251799813685248), (-1412670834764405/4503599627370496)), (885379/4503599627370496), by norm_num⟩
  | 6 => ⟨((-885791455762361/9007199254740992), (-39951082445189/9007199254740992)), (141991/1125899906842624), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4978472343/2147483648), (-33635803767/2147483648)), (1/2147483648), by norm_num⟩, -2, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-2525033459/1073741824), (-68239029227/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-421867684309125/4503599627370496), (153685654910857/9007199254740992)), (2286115/18014398509481984), by norm_num⟩
  | 1 => ⟨((80735088137/274877906944), (-7352912629/137438953472)), (111/274877906944), by norm_num⟩
  | 2 => ⟨((-63286100469/137438953472), (11527507509/137438953472)), (89/137438953472), by norm_num⟩
  | 3 => ⟨((66144400657/137438953472), (-12048144373/137438953472)), (95/137438953472), by norm_num⟩
  | 4 => ⟨((-51848846419/137438953472), (18888443497/274877906944)), (151/274877906944), by norm_num⟩
  | 5 => ⟨((16257175805/68719476736), (-11844921067/274877906944)), (3/8589934592), by norm_num⟩
  | 6 => ⟨((-67965707605/549755813888), (12379893831/549755813888)), (51/274877906944), by norm_num⟩
  | 7 => ⟨((15221863077/274877906944), (-11090595857/1099511627776)), (93/1099511627776), by norm_num⟩
  | 8 => ⟨((-95456127267/4398046511104), (4346812395/1099511627776)), (37/1099511627776), by norm_num⟩
  | 9 => ⟨((33255792769/4398046511104), (-12115026775/8796093022208)), (105/8796093022208), by norm_num⟩
  | 10 => ⟨((-83418676699/35184372088832), (1899329819/4398046511104)), (67/17592186044416), by norm_num⟩
  | 11 => ⟨((95112283015/140737488355328), (-4331154663/35184372088832)), (77/70368744177664), by norm_num⟩
  | 12 => ⟨((-99408004419/562949953421312), (9053540263/281474976710656)), (163/562949953421312), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316641/5070602400912917605986812821504), (1928789331391/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222291376129841/79228162514264337593543950336), (2281578384065/316912650057057350374175801344)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472312223040493/9903520314283042199192993792), (1283118191471/9903520314283042199192993792)), (51/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888992522270513/2475880078570760549798248448), (5451941019565/2475880078570760549798248448)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770658059987185/154742504910672534362390528), (2725232967415/77371252455336267181195264)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549053331511307/9671406556917033397649408), (5108244806579/9671406556917033397649408)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78646896656027/37778931862957161709568), (4468147501709/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887078332975037/75557863725914323419136), (1814450691257/18889465931478580854784)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162125366623187/590295810358705651712), (2720391454717/2361183241434822606848)), (869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((50647137261849/18446744073709551616), (7476902819159/590295810358705651712)), (1195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227818369916127/9223372036854775808), (9339870122533/73786976294838206464)), (747/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910804568755451/4611686018427387904), (1312344004387/1152921504606846976)), (1683/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592852475150497/1152921504606846976), (1311000612337/144115188075855872)), (1685/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193583251867953/144115188075855872), (4582460444553/72057594037927936)), (1477/144115188075855872), by norm_num⟩
  | 4 => ⟨((745064789054877/18014398509481984), (6861616197507/18014398509481984)), (555/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487352767416243/9007199254740992), (17111820103173/9007199254740992)), (2783/9007199254740992), by norm_num⟩
  | 2 => ⟨((34751222093013/70368744177664), (17048570211263/2251799813685248)), (2795/2251799813685248), by norm_num⟩
  | 1 => ⟨((138134380838045/140737488355328), (6353753466391/281474976710656)), (4225/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084118941008237/1125899906842624), (50200368341309/1125899906842624)), (8577/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1084118941008237/1125899906842624), (50200368341309/1125899906842624)), (32718662742232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1041650145047173/1125899906842624), (48337485271691/562949953421312)), (4321/281474976710656), by norm_num⟩
  | 2 => ⟨((955403733679845/1125899906842624), (11180112068237/70368744177664)), (17475/562949953421312), by norm_num⟩
  | 3 => ⟨((782305419048915/1125899906842624), (303587080820555/1125899906842624)), (70421/1125899906842624), by norm_num⟩
  | 4 => ⟨((923415393984599/2251799813685248), (421880874198097/1125899906842624)), (67919/562949953421312), by norm_num⟩
  | 5 => ⟨((62510930561257/2251799813685248), (1384035263861715/4503599627370496)), (852829/4503599627370496), by norm_num⟩
  | 6 => ⟨((-421867684309125/4503599627370496), (153685654910857/9007199254740992)), (2286115/18014398509481984), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2525033459/1073741824), (-68239029227/4294967296)), (1/2147483648), by norm_num⟩, -3, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-5118613975/2147483648), (-69165271335/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1532889014576571/18014398509481984), (160144001150041/4503599627370496)), (578231/4503599627370496), by norm_num⟩
  | 1 => ⟨((74334774845/274877906944), (-15531807137/137438953472)), (57/137438953472), by norm_num⟩
  | 2 => ⟨((-59059978981/137438953472), (12340229791/68719476736)), (23/34359738368), by norm_num⟩
  | 3 => ⟨((15641316035/34359738368), (-13072638185/68719476736)), (99/137438953472), by norm_num⟩
  | 4 => ⟨((-49708944337/137438953472), (2596596741/17179869184)), (5/8589934592), by norm_num⟩
  | 5 => ⟨((63191080381/274877906944), (-26406797499/274877906944)), (13/34359738368), by norm_num⟩
  | 6 => ⟨((-66941551683/549755813888), (13987037323/274877906944)), (7/34359738368), by norm_num⟩
  | 7 => ⟨((1899498703/34359738368), (-25400890023/1099511627776)), (13/137438953472), by norm_num⟩
  | 8 => ⟨((-96587346061/4398046511104), (10090674479/1099511627776)), (167/4398046511104), by norm_num⟩
  | 9 => ⟨((17053321395/2199023255552), (-3563189631/1099511627776)), (15/1099511627776), by norm_num⟩
  | 10 => ⟨((-86714197407/35184372088832), (2264801691/2199023255552)), (77/17592186044416), by norm_num⟩
  | 11 => ⟨((6263236073/8796093022208), (-10469326093/35184372088832)), (91/70368744177664), by norm_num⟩
  | 12 => ⟨((-26539868523/140737488355328), (22181387927/281474976710656)), (49/140737488355328), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790435469823053/5070602400912917605986812821504), (1788330315293/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778283391933843/633825300114114700748351602688), (4230633883561/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889195422233673/39614081257132168796771975168), (4758454875415/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888935839643347/2475880078570760549798248448), (5054626628765/2475880078570760549798248448)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885300761289003/77371252455336267181195264), (631655148767/19342813113834066795298816)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549000481886719/9671406556917033397649408), (36999546015/75557863725914323419136)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258304257161789/604462909807314587353088), (2071238883911/302231454903657293676544)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887003726486191/75557863725914323419136), (1682192061719/18889465931478580854784)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((20264800476265/73786976294838206464), (5044163547921/4722366482869645213696)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620632211087395/590295810358705651712), (1732951424683/147573952589676412928)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822452346428789/73786976294838206464), (4329440363801/36893488147419103232)), (1493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821503540615557/9223372036854775808), (4866582316639/4611686018427387904)), (1681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199093491208495/144115188075855872), (9723075193193/1152921504606846976)), (1683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193492954855815/144115188075855872), (8496348142209/144115188075855872)), (1475/144115188075855872), by norm_num⟩
  | 4 => ⟨((744998243390549/18014398509481984), (12721856845035/36028797018963968)), (2217/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487190508745133/9007199254740992), (15862701556739/9007199254740992)), (1389/4503599627370496), by norm_num⟩
  | 2 => ⟨((17373171529561/35184372088832), (15803362197311/2251799813685248)), (2791/2251799813685248), by norm_num⟩
  | 1 => ⟨((276214019234771/281474976710656), (11778504979173/562949953421312)), (4215/1125899906842624), by norm_num⟩
  | 0 => ⟨((1083741297603209/1125899906842624), (46523780463309/1125899906842624)), (8549/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1083741297603209/1125899906842624), (46523780463309/1125899906842624)), (32611851218795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1041238862226813/1125899906842624), (89563453913245/1125899906842624)), (8583/562949953421312), by norm_num⟩
  | 2 => ⟨((1911638413671067/2251799813685248), (331315237821637/2251799813685248)), (17241/562949953421312), by norm_num⟩
  | 3 => ⟨((787057449838097/1125899906842624), (562532185858805/2251799813685248)), (137387/2251799813685248), by norm_num⟩
  | 4 => ⟨((59990769498017/140737488355328), (393236685573123/1125899906842624)), (260723/2251799813685248), by norm_num⟩
  | 5 => ⟨((134459597797541/2251799813685248), (1340968729117629/4503599627370496)), (808789/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1532889014576571/18014398509481984), (160144001150041/4503599627370496)), (578231/4503599627370496), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5118613975/2147483648), (-69165271335/4294967296)), (1/2147483648), by norm_num⟩, -3, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-5184362399/2147483648), (-70053696919/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-331845223320075/4503599627370496), (114168761718459/2251799813685248)), (2292841/18014398509481984), by norm_num⟩
  | 1 => ⟨((65195835385/274877906944), (-44860237677/274877906944)), (57/137438953472), by norm_num⟩
  | 2 => ⟨((-52464324601/137438953472), (36099883639/137438953472)), (93/137438953472), by norm_num⟩
  | 3 => ⟨((56292048709/137438953472), (-38733680909/137438953472)), (101/137438953472), by norm_num⟩
  | 4 => ⟨((-45299278681/137438953472), (3896215909/17179869184)), (83/137438953472), by norm_num⟩
  | 5 => ⟨((14581275303/68719476736), (-20066296317/137438953472)), (109/274877906944), by norm_num⟩
  | 6 => ⟨((-62580419425/549755813888), (10765152685/137438953472)), (119/549755813888), by norm_num⟩
  | 7 => ⟨((57553885485/1099511627776), (-39601931119/1099511627776)), (111/1099511627776), by norm_num⟩
  | 8 => ⟨((-23157351327/1099511627776), (15934212337/1099511627776)), (91/2199023255552), by norm_num⟩
  | 9 => ⟨((16564586301/2199023255552), (-11397833529/2199023255552)), (33/2199023255552), by norm_num⟩
  | 10 => ⟨((-42655477115/17592186044416), (14675284321/8796093022208)), (43/8796093022208), by norm_num⟩
  | 11 => ⟨((24964124379/35184372088832), (-34354849399/70368744177664)), (51/35184372088832), by norm_num⟩
  | 12 => ⟨((-26785472151/140737488355328), (36861331399/281474976710656)), (111/281474976710656), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058242031/10141204801825835211973625643008), (3307211892881/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778237610194751/633825300114114700748351602688), (977930030549/158456325028528675187087900672)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((59035750210467/1237940039285380274899124224), (4399745327591/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888881326568579/2475880078570760549798248448), (4673576413607/2475880078570760549798248448)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885273569893407/77371252455336267181195264), (4672279546297/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774474818178689/4835703278458516698824704), (1094721119241/2417851639229258349412352)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78641244097569/37778931862957161709568), (3830146683507/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117933244632383/4722366482869645213696), (6221406820505/75557863725914323419136)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296893597602927/4722366482869645213696), (36435914383/36893488147419103232)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405139708344817/147573952589676412928), (6409053010683/590295810358705651712)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822361174846941/73786976294838206464), (8005816920219/73786976294838206464)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821401728467375/9223372036854775808), (2249746640779/2305843009213693952)), (105/576460752303423488), by norm_num⟩
  | 6 => ⟨((796323530339313/576460752303423488), (4494772955427/576460752303423488)), (841/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193405753218079/144115188075855872), (7855240447985/144115188075855872)), (737/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489867795971821/36028797018963968), (11761657502605/36028797018963968)), (2215/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487033327563395/9007199254740992), (7332507110097/4503599627370496)), (347/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111731294139693/2251799813685248), (14609523537707/2251799813685248)), (1393/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104642203839533/1125899906842624), (21775894039313/1125899906842624)), (2103/562949953421312), by norm_num⟩
  | 0 => ⟨((1083367616719313/1125899906842624), (43000236598323/1125899906842624)), (4261/562949953421312), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1083367616719313/1125899906842624), (43000236598323/1125899906842624)), (16254427196311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1040799777570609/1125899906842624), (165503393538883/2251799813685248)), (34103/2251799813685248), by norm_num⟩
  | 2 => ⟨((956049758180917/1125899906842624), (152993968767179/1125899906842624)), (68065/2251799813685248), by norm_num⟩
  | 3 => ⟨((1582066008223139/2251799813685248), (519654885675181/2251799813685248)), (134093/2251799813685248), by norm_num⟩
  | 4 => ⟨((247900772595179/562949953421312), (730196641493017/2251799813685248)), (250313/2251799813685248), by norm_num⟩
  | 5 => ⟨((399759828444339/4503599627370496), (643099126209719/2251799813685248)), (765591/4503599627370496), by norm_num⟩
  | 6 => ⟨((-331845223320075/4503599627370496), (114168761718459/2251799813685248)), (2292841/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5184362399/2147483648), (-70053696919/4294967296)), (1/2147483648), by norm_num⟩, -3, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-5247531779/2147483648), (-70907273167/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-544217652743785/9007199254740992), (1123890012569785/18014398509481984)), (1118177/9007199254740992), by norm_num⟩
  | 1 => ⟨((54111134349/274877906944), (-27936875603/137438953472)), (57/137438953472), by norm_num⟩
  | 2 => ⟨((-44074824873/137438953472), (45510518843/137438953472)), (95/137438953472), by norm_num⟩
  | 3 => ⟨((47866678111/137438953472), (-24712943981/68719476736)), (105/137438953472), by norm_num⟩
  | 4 => ⟨((-2436785285/8589934592), (20129289307/68719476736)), (87/137438953472), by norm_num⟩
  | 5 => ⟨((25405701443/137438953472), (-52466534243/274877906944)), (115/274877906944), by norm_num⟩
  | 6 => ⟨((-13795704653/137438953472), (28490172263/274877906944)), (127/549755813888), by norm_num⟩
  | 7 => ⟨((51368842937/1099511627776), (-53042132353/1099511627776)), (15/137438953472), by norm_num⟩
  | 8 => ⟨((-20920581167/1099511627776), (43204096947/2199023255552)), (99/2199023255552), by norm_num⟩
  | 9 => ⟨((3786737393/549755813888), (-62561386085/8796093022208)), (145/8796093022208), by norm_num⟩
  | 10 => ⟨((-19740089585/8796093022208), (40766207083/17592186044416)), (3/549755813888), by norm_num⟩
  | 11 => ⟨((5846828867/8796093022208), (-6037283553/8796093022208)), (115/70368744177664), by norm_num⟩
  | 12 => ⟨((-50798754373/281474976710656), (52453473715/281474976710656)), (127/281474976710656), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((6174971645405/39614081257132168796771975168), (1524166268711/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889096761997801/316912650057057350374175801344), (901336602289/158456325028528675187087900672)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889094489444153/39614081257132168796771975168), (2027570792711/19807040628566084398385987584)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888828818413099/2475880078570760549798248448), (4307512670239/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770494748502581/154742504910672534362390528), (2153151646467/77371252455336267181195264)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548900643623269/9671406556917033397649408), (4035874709109/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78638572557671/37778931862957161709568), (1765053059703/302231454903657293676544)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943431343197595/37778931862957161709568), (716751909283/9444732965739290427392)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296841879892879/4722366482869645213696), (4298405983065/4722366482869645213696)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620488051174863/590295810358705651712), (5906888335279/590295810358705651712)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822273190929403/73786976294838206464), (1844620802371/18446744073709551616)), (1491/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821303424560447/9223372036854775808), (8293747966729/9223372036854775808)), (1679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199068700341625/144115188075855872), (2071236828723/288230376151711744)), (1681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193321427107985/144115188075855872), (3619718485051/72057594037927936)), (23/2251799813685248), by norm_num⟩
  | 4 => ⟨((1489743200712277/36028797018963968), (2709848399351/9007199254740992)), (553/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486880885963139/9007199254740992), (13514708241269/9007199254740992)), (693/2251799813685248), by norm_num⟩
  | 2 => ⟨((1111583782572659/2251799813685248), (26926013140589/4503599627370496)), (5563/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208866357786835/2251799813685248), (40131203828077/2251799813685248)), (8395/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082998041930599/1125899906842624), (79235296810605/2251799813685248)), (531/70368744177664), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1082998041930599/1125899906842624), (79235296810605/2251799813685248)), (2025604516482331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2080673767964117/2251799813685248), (152432149209991/2251799813685248)), (16943/1125899906842624), by norm_num⟩
  | 2 => ⟨((1912233823989071/2251799813685248), (281696065811961/2251799813685248)), (33605/1125899906842624), by norm_num⟩
  | 3 => ⟨((794316950905911/1125899906842624), (29902122174479/140737488355328)), (130967/2251799813685248), by norm_num⟩
  | 4 => ⟨((1019121953444229/2251799813685248), (675065692554659/2251799813685248)), (120223/1125899906842624), by norm_num⟩
  | 5 => ⟨((258857764879963/2251799813685248), (1222087795048817/4503599627370496)), (723619/4503599627370496), by norm_num⟩
  | 6 => ⟨((-544217652743785/9007199254740992), (1123890012569785/18014398509481984)), (1118177/9007199254740992), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5247531779/2147483648), (-70907273167/4294967296)), (1/2147483648), by norm_num⟩, -3, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-165884901/67108864), (-71728631195/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-831109996062555/18014398509481984), (1273716368947615/18014398509481984)), (269031/2251799813685248), by norm_num⟩
  | 1 => ⟨((20898460119/137438953472), (-64055806971/274877906944)), (55/137438953472), by norm_num⟩
  | 2 => ⟨((-8609739413/34359738368), (13194843131/34359738368)), (93/137438953472), by norm_num⟩
  | 3 => ⟨((18917531043/68719476736), (-57984067243/137438953472)), (13/17179869184), by norm_num⟩
  | 4 => ⟨((-31174548113/137438953472), (47776506615/137438953472)), (87/137438953472), by norm_num⟩
  | 5 => ⟨((41098489981/274877906944), (-62985428733/274877906944)), (117/274877906944), by norm_num⟩
  | 6 => ⟨((-45151306139/549755813888), (69196566013/549755813888)), (65/274877906944), by norm_num⟩
  | 7 => ⟨((42517525521/1099511627776), (-65160169505/1099511627776)), (31/274877906944), by norm_num⟩
  | 8 => ⟨((-4379088377/274877906944), (53689322213/2199023255552)), (13/274877906944), by norm_num⟩
  | 9 => ⟨((12829120811/2199023255552), (-9830624859/1099511627776)), (155/8796093022208), by norm_num⟩
  | 10 => ⟨((-16913075731/8796093022208), (25920108661/8796093022208)), (103/17592186044416), by norm_num⟩
  | 11 => ⟨((40540173463/70368744177664), (-62129781597/70368744177664)), (125/70368744177664), by norm_num⟩
  | 12 => ⟨((-44537932751/281474976710656), (68256541555/281474976710656)), (139/281474976710656), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (2799224578541/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778151009038225/633825300114114700748351602688), (413820606221/79228162514264337593543950336)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472261682866179/9903520314283042199192993792), (3723577416433/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888778168775427/2475880078570760549798248448), (988825631273/618970019642690137449562112)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885222101823709/77371252455336267181195264), (1977089778551/77371252455336267181195264)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548853369079617/9671406556917033397649408), (1852925260079/4835703278458516698824704)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258175906872613/604462909807314587353088), (3241426771495/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886795856842733/75557863725914323419136), (1316270875013/18889465931478580854784)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648395969898771/2361183241434822606848), (1973428903083/2361183241434822606848)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810209839538885/295147905179352825856), (2711877209961/295147905179352825856)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455547042133799/18446744073709551616), (846866635483/9223372036854775808)), (745/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821208382185073/9223372036854775808), (7615259112423/9223372036854775808)), (839/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796227659366991/576460752303423488), (3803544909815/576460752303423488)), (105/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193239779864499/144115188075855872), (1661755506213/36028797018963968)), (1471/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489622427570413/36028797018963968), (1244024013725/4503599627370496)), (1105/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486732879796477/9007199254740992), (1551024181421/1125899906842624)), (173/562949953421312), by norm_num⟩
  | 2 => ⟨((2222880390661377/4503599627370496), (24720446448867/4503599627370496)), (5555/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104228770408647/1125899906842624), (9210379124267/562949953421312)), (8379/2251799813685248), by norm_num⟩
  | 0 => ⟨((270658166615111/281474976710656), (72730602780671/2251799813685248)), (16943/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((270658166615111/281474976710656), (72730602780671/2251799813685248)), (64632424361418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((519926792882171/562949953421312), (69935636323593/1125899906842624)), (33679/2251799813685248), by norm_num⟩
  | 2 => ⟨((1912078471731203/2251799813685248), (129181682602207/1125899906842624)), (66395/2251799813685248), by norm_num⟩
  | 3 => ⟨((199245756203791/281474976710656), (438769934599913/2251799813685248)), (127993/2251799813685248), by norm_num⟩
  | 4 => ⟨((1042814151415295/2251799813685248), (621178112814729/2251799813685248)), (57771/562949953421312), by norm_num⟩
  | 5 => ⟨((155786296430079/1125899906842624), (1150676579073899/4503599627370496)), (683049/4503599627370496), by norm_num⟩
  | 6 => ⟨((-831109996062555/18014398509481984), (1273716368947615/18014398509481984)), (269031/2251799813685248), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-71728631195/4294967296)), (1/2147483648), by norm_num⟩, -3, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile011Terms3
