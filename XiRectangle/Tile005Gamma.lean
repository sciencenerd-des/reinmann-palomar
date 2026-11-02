/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile005Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1551/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1551/640))
  have he : value ((3/4), (1551/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_halfVariable : Sound J_halfVariable F_halfVariable c := by
  apply sound_round (sound_scale (A_variable hcre) S_variable)
  intro k
  fin_cases k <;> norm_num [J_halfVariable, J_variable, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(1, 0), 0, by norm_num⟩
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

theorem S_q0 : Sound J_q0 F_q0 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (1, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_base : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_base : Sound J_base F_base c := by
  apply sound_round (sound_add (A_q0 hcre) (A_halfVariable hcre) S_q0 S_halfVariable)
  intro k
  fin_cases k <;> norm_num [J_base, J_q0, J_halfVariable, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(12, 0), 0, by norm_num⟩
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

theorem S_q1 : Sound J_q1 F_q1 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (12, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((107/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_shift : Sound J_shift F_shift c := by
  apply sound_round (sound_add (A_base hcre) (A_q1 hcre) S_base S_q1)
  intro k
  fin_cases k <;> norm_num [J_shift, J_base, J_q1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftInv : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21913600/295500001), (-1985280/295500001)), 0, by norm_num⟩
  | 1 => ⟨((-238132264140800/87320250591000001), (43504631808000/87320250591000001)), 0, by norm_num⟩
  | 2 => ⟨((27991175207/281474976710656), (-31113438813/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-64752102123/18014398509481984), (97904701831/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((296795310745/2305843009213693952), (-144008050261/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-336674512269/73786976294838206464), (202772607353/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((94418817821/590295810358705651712), (-138392445805/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-209183872461/37778931862957161709568), (23063094891/4722366482869645213696)), (9/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((228368356553/1208925819614629174706176), (-60351296553/302231454903657293676544)), (13/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-122507368251/19342813113834066795298816), (77745269713/9671406556917033397649408)), (9/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((32160882555/154742504910672534362390528), (-24707742135/77371252455336267181195264)), (13/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-65695527991/9903520314283042199192993792), (62089719615/4951760157141521099596496896)), (9/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((129201441465/633825300114114700748351602688), (-308807316973/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (1551/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (1551/1280)))⁻¹=value ((21913600/295500001), (-1985280/295500001)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/295500001), (-1985280/295500001))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89248538815/34359738368), (3104373153/34359738368)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((10956800/295500001), (-992640/295500001)), 0, by norm_num⟩
  | 2 => ⟨((-59533066035200/87320250591000001), (10876157952000/87320250591000001)), 0, by norm_num⟩
  | 3 => ⟨((298572535541/18014398509481984), (-10371146271/2251799813685248)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-64752102123/144115188075855872), (97904701831/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((59359062149/4611686018427387904), (-115206440209/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-112224837423/295147905179352825856), (135181738235/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 7 => ⟨((107907220367/9444732965739290427392), (-79081397603/9444732965739290427392)), (1/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-209183872461/604462909807314587353088), (23063094891/75557863725914323419136)), (9/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((101497047357/9671406556917033397649408), (-6705699617/604462909807314587353088)), (3/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-98005894601/309485009821345068724781056), (124392431541/309485009821345068724781056)), (1/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((93558931069/9903520314283042199192993792), (-71877068029/4951760157141521099596496896)), (5/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-175188074643/633825300114114700748351602688), (20696573205/39614081257132168796771975168)), (25/633825300114114700748351602688), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (33/20480)), 0, by norm_num⟩
  | 45 => ⟨((107073747473/4080638361600), (-65571/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-51456012419479/1915179604377600), (1389317039803/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((483543011397/17592186044416), (-42560856833/17592186044416)), (1/17592186044416), by norm_num⟩
  | 42 => ⟨((-123742402757/4398046511104), (10900630977/4398046511104)), (1/17592186044416), by norm_num⟩
  | 41 => ⟨((253490767737/8796093022208), (-11159696619/4398046511104)), (1/8796093022208), by norm_num⟩
  | 40 => ⟨((-64950088233/2199023255552), (22859245217/8796093022208)), (1/8796093022208), by norm_num⟩
  | 39 => ⟨((66608289031/2199023255552), (-11712827425/4398046511104)), (1/8796093022208), by norm_num⟩
  | 38 => ⟨((-34176717533/1099511627776), (750653115/274877906944)), (1/8796093022208), by norm_num⟩
  | 37 => ⟨((280770024697/8796093022208), (-12323606789/4398046511104)), (1/8796093022208), by norm_num⟩
  | 36 => ⟨((-72133289071/2199023255552), (12653538719/4398046511104)), (1/8796093022208), by norm_num⟩
  | 35 => ⟨((74184462045/2199023255552), (-26003257109/8796093022208)), (1/8796093022208), by norm_num⟩
  | 34 => ⟨((-38177860235/1099511627776), (13369417637/4398046511104)), (1/8796093022208), by norm_num⟩
  | 33 => ⟨((314631718205/8796093022208), (-27517254703/8796093022208)), (1/8796093022208), by norm_num⟩
  | 32 => ⟨((-162206612435/4398046511104), (14171185809/4398046511104)), (1/8796093022208), by norm_num⟩
  | 31 => ⟨((334822544461/8796093022208), (-29218519551/8796093022208)), (1/8796093022208), by norm_num⟩
  | 30 => ⟨((-43240266899/1099511627776), (15075292777/4398046511104)), (1/8796093022208), by norm_num⟩
  | 29 => ⟨((178891512965/4398046511104), (-31144101521/8796093022208)), (1/8796093022208), by norm_num⟩
  | 28 => ⟨((-370486338821/8796093022208), (32205354215/8796093022208)), (1/8796093022208), by norm_num⟩
  | 27 => ⟨((48015643567/1099511627776), (-8335379659/2199023255552)), (1/4398046511104), by norm_num⟩
  | 26 => ⟨((-398806768311/8796093022208), (34560820703/8796093022208)), (1/8796093022208), by norm_num⟩
  | 25 => ⟨((414655581661/8796093022208), (-35872737071/8796093022208)), (1/8796093022208), by norm_num⟩
  | 24 => ⟨((-215908289017/4398046511104), (37288242369/8796093022208)), (1/8796093022208), by norm_num⟩
  | 23 => ⟨((112614951371/2199023255552), (-9705029381/2199023255552)), (1/8796093022208), by norm_num⟩
  | 22 => ⟨((-117696507605/2199023255552), (20241668779/4398046511104)), (1/8796093022208), by norm_num⟩
  | 21 => ⟨((493034004403/8796093022208), (-42295563837/8796093022208)), (1/8796093022208), by norm_num⟩
  | 20 => ⟨((-258744948487/4398046511104), (22138887581/4398046511104)), (1/4398046511104), by norm_num⟩
  | 19 => ⟨((68062460925/1099511627776), (-23227542841/4398046511104)), (1/2199023255552), by norm_num⟩
  | 18 => ⟨((-35905353649/549755813888), (12214454383/2199023255552)), (1/4398046511104), by norm_num⟩
  | 17 => ⟨((75996083635/1099511627776), (-25761462965/4398046511104)), (1/4398046511104), by norm_num⟩
  | 16 => ⟨((-2521869991/34359738368), (6811989971/1099511627776)), (1/4398046511104), by norm_num⟩
  | 15 => ⟨((172049408279/2199023255552), (-7229186411/1099511627776)), (1/4398046511104), by norm_num⟩
  | 14 => ⟨((-92102489069/1099511627776), (7700897581/1099511627776)), (1/4398046511104), by norm_num⟩
  | 13 => ⟨((396420698039/4398046511104), (-32954292269/4398046511104)), (1/4398046511104), by norm_num⟩
  | 12 => ⟨((-429045938333/4398046511104), (35428463119/4398046511104)), (1/4398046511104), by norm_num⟩
  | 11 => ⟨((467529676043/4398046511104), (-9576292559/1099511627776)), (1/4398046511104), by norm_num⟩
  | 10 => ⟨((-256803897637/2199023255552), (20845798329/2199023255552)), (1/2199023255552), by norm_num⟩
  | 9 => ⟨((142444551973/1099511627776), (-22868394903/2199023255552)), (1/2199023255552), by norm_num⟩
  | 8 => ⟨((-159942823315/1099511627776), (12663593923/1099511627776)), (1/2199023255552), by norm_num⟩
  | 7 => ⟨((182354664495/1099511627776), (-14190478249/1099511627776)), (1/2199023255552), by norm_num⟩
  | 6 => ⟨((-212094820821/1099511627776), (2017285715/137438953472)), (1/2199023255552), by norm_num⟩
  | 5 => ⟨((506953881267/2199023255552), (-18710141949/1099511627776)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((-315047003153/1099511627776), (22266055267/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((416505012589/1099511627776), (-27512297245/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((-308002547307/549755813888), (18028334797/549755813888)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((299461076175/274877906944), (-1642722033/34359738368)), (1/137438953472), by norm_num⟩
  | 0 => ⟨((-192540297063/1099511627776), (99339940897/1099511627776)), (3/1099511627776), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (1551/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (1551/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (1551/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((89248538815/34359738368), (3104373153/34359738368)), (1/137438953472), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (1551/1280))) (z:=((-21/128), (1551/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((89248538815/34359738368), (3104373153/34359738368))) (r:=(1/137438953472)) (by norm_num) ?_ hs
  norm_num [J_shiftLog,RectangleLogInputs.log2Disk,logTable,inflate,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

set_option maxHeartbeats 5000000 in
theorem S_shiftLog : Sound J_shiftLog F_shiftLog c := by
  apply log_coefficients_sound (A_shift hcre) (L_shiftLog hcre) S_shift S_shiftInv
  · exact logValue
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftLog,J_shift,J_shiftInv,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 0), 0, by norm_num⟩
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

theorem S_q2 : Sound J_q2 F_q2 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact ((-1/2), 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shiftMinusHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_shiftMinusHalf : Sound J_shiftMinusHalf F_shiftMinusHalf c := by
  apply sound_round (sound_add (A_shift hcre) (A_q2 hcre) S_shift S_q2)
  intro k
  fin_cases k <;> norm_num [J_shiftMinusHalf, J_shift, J_q2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainLead : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((143164163761/4294967296), (37028233059/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((489337030491/274877906944), (12879175869/274877906944)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((839200135756800/87320250591000001), (-78769359224160/87320250591000001)), 0, by norm_num⟩
  | 3 => ⟨((-274532218599/2251799813685248), (51930992599/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((41368573325/18014398509481984), (-47603628949/72057594037927936)), (19/144115188075855872), by norm_num⟩
  | 5 => ⟨((-236886257869/4611686018427387904), (46362283245/2305843009213693952)), (31/4611686018427387904), by norm_num⟩
  | 6 => ⟨((93173520877/73786976294838206464), (-93702010753/147573952589676412928)), (21/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-310467524291/9444732965739290427392), (1515891515/73786976294838206464)), (105/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((134055204427/151115727451828646838272), (-204288984991/302231454903657293676544)), (129/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-118344871821/4835703278458516698824704), (108824913637/4835703278458516698824704)), (157/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((52849555767/77371252455336267181195264), (-29232765745/38685626227668133590597632)), (105/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-189333494051/9903520314283042199192993792), (63202878479/2475880078570760549798248448)), (135/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((42135565021/79228162514264337593543950336), (-17153654639/19807040628566084398385987584)), (337/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((-1/2), 0), 0, by norm_num⟩
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
theorem S_negativeShift : Sound J_negativeShift F_negativeShift c := by
  apply sound_round (sound_scale (A_shift hcre) S_shift)
  intro k
  fin_cases k <;> norm_num [J_negativeShift, J_shift, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainMinusShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((85718976177/4294967296), (53239296505/17179869184)), (5/17179869184), by norm_num⟩
  | 1 => ⟨((351898077019/274877906944), (12879175869/274877906944)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((839200135756800/87320250591000001), (-78769359224160/87320250591000001)), 0, by norm_num⟩
  | 3 => ⟨((-274532218599/2251799813685248), (51930992599/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((41368573325/18014398509481984), (-47603628949/72057594037927936)), (19/144115188075855872), by norm_num⟩
  | 5 => ⟨((-236886257869/4611686018427387904), (46362283245/2305843009213693952)), (31/4611686018427387904), by norm_num⟩
  | 6 => ⟨((93173520877/73786976294838206464), (-93702010753/147573952589676412928)), (21/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-310467524291/9444732965739290427392), (1515891515/73786976294838206464)), (105/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((134055204427/151115727451828646838272), (-204288984991/302231454903657293676544)), (129/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-118344871821/4835703278458516698824704), (108824913637/4835703278458516698824704)), (157/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((52849555767/77371252455336267181195264), (-29232765745/38685626227668133590597632)), (105/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-189333494051/9903520314283042199192993792), (63202878479/2475880078570760549798248448)), (135/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((42135565021/79228162514264337593543950336), (-17153654639/19807040628566084398385987584)), (337/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainMinusShift : Sound J_mainMinusShift F_mainMinusShift c := by
  apply sound_round (sound_add (A_mainLead hcre) (A_negativeShift hcre) S_mainLead S_negativeShift)
  intro k
  fin_cases k <;> norm_num [J_mainMinusShift, J_mainLead, J_negativeShift, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((505191801235/274877906944), 0), (1/274877906944), by norm_num⟩
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
theorem S_logTwoPi : Sound J_logTwoPi F_logTwoPi c := by
  apply sound_round (sound_add (A_log2 hcre) (A_logpi hcre) S_log2 S_logpi)
  intro k
  fin_cases k <;> norm_num [J_logTwoPi, J_log2, J_logpi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_halfLogTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((505191801235/549755813888), 0), (1/549755813888), by norm_num⟩
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
theorem S_halfLogTwoPi : Sound J_halfLogTwoPi F_halfLogTwoPi c := by
  apply sound_round (sound_scale (A_logTwoPi hcre) S_logTwoPi)
  intro k
  fin_cases k <;> norm_num [J_halfLogTwoPi, J_logTwoPi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainConstant : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358663148497/17179869184), (53239296505/17179869184)), (3/8589934592), by norm_num⟩
  | 1 => ⟨((351898077019/274877906944), (12879175869/274877906944)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((839200135756800/87320250591000001), (-78769359224160/87320250591000001)), 0, by norm_num⟩
  | 3 => ⟨((-274532218599/2251799813685248), (51930992599/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((41368573325/18014398509481984), (-47603628949/72057594037927936)), (19/144115188075855872), by norm_num⟩
  | 5 => ⟨((-236886257869/4611686018427387904), (46362283245/2305843009213693952)), (31/4611686018427387904), by norm_num⟩
  | 6 => ⟨((93173520877/73786976294838206464), (-93702010753/147573952589676412928)), (21/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-310467524291/9444732965739290427392), (1515891515/73786976294838206464)), (105/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((134055204427/151115727451828646838272), (-204288984991/302231454903657293676544)), (129/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-118344871821/4835703278458516698824704), (108824913637/4835703278458516698824704)), (157/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((52849555767/77371252455336267181195264), (-29232765745/38685626227668133590597632)), (105/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-189333494051/9903520314283042199192993792), (63202878479/2475880078570760549798248448)), (135/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((42135565021/79228162514264337593543950336), (-17153654639/19807040628566084398385987584)), (337/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((476264528281600/87320250591000001), (-87009263616000/87320250591000001)), 0, by norm_num⟩
  | 1 => ⟨((-27991175207/70368744177664), (31113438813/281474976710656)), (1/562949953421312), by norm_num⟩
  | 2 => ⟨((388512612737/18014398509481984), (-146857052747/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 3 => ⟨((-296795310745/288230376151711744), (144008050261/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((26302696271/576460752303423488), (-126732879595/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-283256453463/147573952589676412928), (207588668707/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((45758972101/590295810358705651712), (-161441664237/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-228368356553/75557863725914323419136), (60351296553/18889465931478580854784)), (3/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((68910394641/604462909807314587353088), (-87463428427/604462909807314587353088)), (5/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-160804412775/38685626227668133590597632), (247077421351/38685626227668133590597632)), (15/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((180662701975/1237940039285380274899124224), (-170746728941/618970019642690137449562112)), (23/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-96901081099/19807040628566084398385987584), (115802743865/9903520314283042199192993792)), (17/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((97585774041/633825300114114700748351602688), (-77247507155/158456325028528675187087900672)), (25/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((27991175207/70368744177664), (-31113438813/281474976710656)), (1/562949953421312), by norm_num⟩
  | 1 => ⟨((-388512612737/9007199254740992), (146857052747/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 2 => ⟨((222596483059/72057594037927936), (-1687594339/1125899906842624)), (3/72057594037927936), by norm_num⟩
  | 3 => ⟨((-26302696271/144115188075855872), (126732879595/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 4 => ⟨((88517641707/9223372036854775808), (-64871458971/9223372036854775808)), (5/18446744073709551616), by norm_num⟩
  | 5 => ⟨((-137276916303/295147905179352825856), (242162496355/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 6 => ⟨((12488894499/590295810358705651712), (-13201846121/590295810358705651712)), (5/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-68910394641/75557863725914323419136), (87463428427/75557863725914323419136)), (9/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((45226241093/1208925819614629174706176), (-277962099019/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-112914188735/77371252455336267181195264), (213433411177/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((133238986511/2475880078570760549798248448), (-79614386407/618970019642690137449562112)), (11/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-73189330531/39614081257132168796771975168), (231742521465/39614081257132168796771975168)), (9/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((36125777401/633825300114114700748351602688), (-329974502007/1267650600228229401496703205376)), (7/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((64752102123/2251799813685248), (-97904701831/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 1 => ⟨((-296795310745/72057594037927936), (144008050261/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((26302696271/72057594037927936), (-31683219899/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 3 => ⟨((-236047044553/9223372036854775808), (172990557255/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 4 => ⟨((228794860505/147573952589676412928), (-25225260037/18446744073709551616)), (1/18446744073709551616), by norm_num⟩
  | 5 => ⟨((-12488894499/147573952589676412928), (13201846121/147573952589676412928)), (9/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((160790920829/37778931862957161709568), (-204081332997/37778931862957161709568)), (5/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-120603309581/604462909807314587353088), (185308066013/604462909807314587353088)), (5/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((84685641551/9671406556917033397649408), (-320150116765/19342813113834066795298816)), (19/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-111032488759/309485009821345068724781056), (33172661003/38685626227668133590597632)), (9/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((33545109827/2475880078570760549798248448), (-53107661169/1237940039285380274899124224)), (1/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-36125777401/79228162514264337593543950336), (329974502007/158456325028528675187087900672)), (27/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((15705581875/1267650600228229401496703205376), (-15597226711/158456325028528675187087900672)), (23/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((296795310745/144115188075855872), (-144008050261/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 1 => ⟨((-210421570169/576460752303423488), (126732879595/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 2 => ⟨((88517641707/2305843009213693952), (-64871458971/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-228794860505/73786976294838206464), (25225260037/9223372036854775808)), (7/73786976294838206464), by norm_num⟩
  | 4 => ⟨((249777889981/1180591620717411303424), (-264036922419/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-60296595311/4722366482869645213696), (306121999495/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((211055791767/302231454903657293676544), (-324289115523/302231454903657293676544)), (1/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-84685641551/2417851639229258349412352), (320150116765/4835703278458516698824704)), (9/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((62455774927/38685626227668133590597632), (-298553949027/77371252455336267181195264)), (19/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-83862774567/1237940039285380274899124224), (265538305845/1237940039285380274899124224)), (19/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((24836471963/9903520314283042199192993792), (-113428735065/9903520314283042199192993792)), (9/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-47116745625/633825300114114700748351602688), (374333441063/633825300114114700748351602688)), (33/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((10444338755/10141204801825835211973625643008), (-37435005973/1267650600228229401496703205376)), (29/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((336674512269/2305843009213693952), (-202772607353/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((-35407056683/1152921504606846976), (103794334353/4611686018427387904)), (7/9223372036854775808), by norm_num⟩
  | 2 => ⟨((137276916303/36893488147419103232), (-242162496355/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-12488894499/36893488147419103232), (13201846121/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 4 => ⟨((241186381245/9444732965739290427392), (-153060999747/4722366482869645213696)), (13/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-126633475061/75557863725914323419136), (194573469313/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((118559898171/1208925819614629174706176), (-224105081735/1208925819614629174706176)), (13/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-99929239883/19342813113834066795298816), (238843159221/19342813113834066795298816)), (15/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((37738248555/154742504910672534362390528), (-238984475261/309485009821345068724781056)), (1/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-24836471963/2475880078570760549798248448), (113428735065/2475880078570760549798248448)), (17/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((12957105047/39614081257132168796771975168), (-205883392585/79228162514264337593543950336)), (17/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-6266603253/1267650600228229401496703205376), (359376057341/2535301200456458802993406410752)), (17/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-2103735251/5070602400912917605986812821504), (-151496656683/20282409603651670423947251286016)), (1/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((94418817821/9223372036854775808), (-138392445805/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-45758972101/18446744073709551616), (40360416059/18446744073709551616)), (7/73786976294838206464), by norm_num⟩
  | 2 => ⟨((199822311985/590295810358705651712), (-211229537935/590295810358705651712)), (1/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-160790920829/4722366482869645213696), (204081332997/4722366482869645213696)), (9/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((26381973971/9444732965739290427392), (-162144557761/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-29639974543/151115727451828646838272), (224105081735/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((58292056599/4835703278458516698824704), (-34831294053/1208925819614629174706176)), (17/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-12579416185/19342813113834066795298816), (159322983507/77371252455336267181195264)), (11/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((74509415889/2475880078570760549798248448), (-340286205195/2475880078570760549798248448)), (25/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-10797587539/9903520314283042199192993792), (343138987641/39614081257132168796771975168)), (7/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((11488772631/633825300114114700748351602688), (-164714026281/316912650057057350374175801344)), (15/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((2103735251/1267650600228229401496703205376), (151496656683/5070602400912917605986812821504)), (31/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-39404258447/162259276829213363391578010288128), (-134137303985/81129638414606681695789005144064)), (31/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((209183872461/295147905179352825856), (-23063094891/36893488147419103232)), (9/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-114184178277/590295810358705651712), (241405186211/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((137820789283/4722366482869645213696), (-87463428427/2361183241434822606848)), (1/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-120603309581/37778931862957161709568), (185308066013/37778931862957161709568)), (9/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((84685641551/302231454903657293676544), (-320150116765/604462909807314587353088)), (1/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-24982309971/1208925819614629174706176), (238843159221/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((100635329481/77371252455336267181195264), (-318645967013/77371252455336267181195264)), (21/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((-5322101135/77371252455336267181195264), (194449260111/618970019642690137449562112)), (7/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((55530450201/19807040628566084398385987584), (-110294674599/4951760157141521099596496896)), (35/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((-16412532329/316912650057057350374175801344), (117652875915/79228162514264337593543950336)), (21/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-26446957441/5070602400912917605986812821504), (-476132349575/5070602400912917605986812821504)), (47/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((67550157337/81129638414606681695789005144064), (459899327949/81129638414606681695789005144064)), (51/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-102589114705/1298074214633706907132624082305024), (-426249146431/1298074214633706907132624082305024)), (53/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((228368356553/4722366482869645213696), (-60351296553/1180591620717411303424)), (13/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-137820789283/9444732965739290427392), (174926856853/9444732965739290427392)), (9/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((180904964373/75557863725914323419136), (-277962099019/75557863725914323419136)), (7/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-84685641551/302231454903657293676544), (320150116765/604462909807314587353088)), (17/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((62455774927/2417851639229258349412352), (-298553949027/4835703278458516698824704)), (17/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((-75476497111/38685626227668133590597632), (59746118815/9671406556917033397649408)), (15/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((37254707945/309485009821345068724781056), (-170143102597/309485009821345068724781056)), (3/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((-27765225101/4951760157141521099596496896), (441178698395/9903520314283042199192993792)), (17/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((18464098871/158456325028528675187087900672), (-264718970809/79228162514264337593543950336)), (23/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((16529348401/1267650600228229401496703205376), (74395679621/316912650057057350374175801344)), (29/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-46440733169/20282409603651670423947251286016), (-316180787965/20282409603651670423947251286016)), (17/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((19235459007/81129638414606681695789005144064), (19980428739/20282409603651670423947251286016)), (5/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((-52357372571/2596148429267413814265248164610048), (-154602117541/2596148429267413814265248164610048)), (43/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((122507368251/37778931862957161709568), (-77745269713/18889465931478580854784)), (9/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((-20100551597/18889465931478580854784), (247077421349/151115727451828646838272)), (7/75557863725914323419136), by norm_num⟩
  | 2 => ⟨((112914188735/604462909807314587353088), (-26679176397/75557863725914323419136)), (3/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-13879061095/604462909807314587353088), (265381288023/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((83862774567/38685626227668133590597632), (-265538305845/38685626227668133590597632)), (17/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-49672943927/309485009821345068724781056), (113428735065/154742504910672534362390528)), (1/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((43190350157/4951760157141521099596496896), (-343138987641/4951760157141521099596496896)), (13/2475880078570760549798248448), by norm_num⟩
  | 7 => ⟨((-16412532331/79228162514264337593543950336), (117652875915/19807040628566084398385987584)), (5/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-16529348401/633825300114114700748351602688), (-74395679621/158456325028528675187087900672)), (29/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((51600814633/10141204801825835211973625643008), (351311986627/10141204801825835211973625643008)), (19/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((-23510005453/40564819207303340847894502572032), (-390728384229/162259276829213363391578010288128)), (47/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((69809830095/1298074214633706907132624082305024), (103068078361/649037107316853453566312041152512)), (29/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((-45932855255/10384593717069655257060992658440192), (-51861510097/5192296858534827628530496329220096)), (33/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((32160882555/151115727451828646838272), (-24707742135/75557863725914323419136)), (13/604462909807314587353088), by norm_num⟩
  | 1 => ⟨((-180662701977/2417851639229258349412352), (341493457881/2417851639229258349412352)), (21/2417851639229258349412352), by norm_num⟩
  | 2 => ⟨((8327436657/604462909807314587353088), (-318457545627/9671406556917033397649408)), (5/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((-33545109827/19342813113834066795298816), (53107661169/9671406556917033397649408)), (15/38685626227668133590597632), by norm_num⟩
  | 4 => ⟨((49672943927/309485009821345068724781056), (-113428735065/154742504910672534362390528)), (1/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-51828420189/4951760157141521099596496896), (205883392585/2475880078570760549798248448)), (1/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((11488772631/39614081257132168796771975168), (-164714026281/19807040628566084398385987584)), (7/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((206616855/4951760157141521099596496896), (476132349575/633825300114114700748351602688)), (11/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((-46440733169/5070602400912917605986812821504), (-316180787965/5070602400912917605986812821504)), (17/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((94040021813/81129638414606681695789005144064), (97682096057/20282409603651670423947251286016)), (47/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((-4799425819/40564819207303340847894502572032), (-113374886197/324518553658426726783156020576256)), (31/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((110238852613/10384593717069655257060992658440192), (124467624233/5192296858534827628530496329220096)), (39/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((-72215000765/83076749736557242056487941267521536), (-64972743363/41538374868278621028243970633760768)), (47/166153499473114484112975882535043072), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/886500003), (-165440/295500001)), 0, by norm_num⟩
  | 1 => ⟨((-59533066035200/261960751773000003), (3625385984000/87320250591000001)), 0, by norm_num⟩
  | 2 => ⟨((298572535541/36028797018963968), (-10371146271/4503599627370496)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((-21584034041/72057594037927936), (130539602441/1152921504606846976)), (5/1152921504606846976), by norm_num⟩
  | 4 => ⟨((197863540497/18446744073709551616), (-96005366841/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-112224837423/295147905179352825856), (135181738235/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 6 => ⟨((251783514189/18889465931478580854784), (-184523261073/18889465931478580854784)), (9/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-69727957487/151115727451828646838272), (7687698297/18889465931478580854784)), (3/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((152245571035/9671406556917033397649408), (-20117098851/1208925819614629174706176)), (9/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-40835789417/77371252455336267181195264), (207320719235/309485009821345068724781056)), (13/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((10720294185/618970019642690137449562112), (-8235914045/309485009821345068724781056)), (9/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-175188074643/316912650057057350374175801344), (20696573205/19807040628566084398385987584)), (25/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((43067147155/2535301200456458802993406410752), (-205871544649/5070602400912917605986812821504)), (17/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179384658397/8589934592), (6653709763/2147483648)), (7/17179869184), by norm_num⟩
  | 1 => ⟨((351835608407/274877906944), (12890588325/274877906944)), (3/274877906944), by norm_num⟩
  | 2 => ⟨((338434555707/35184372088832), (-31819944537/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-275206719663/2251799813685248), (6523244095/281474976710656)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((166247197755/72057594037927936), (-47978649913/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 5 => ⟨((-119319885477/2305843009213693952), (23445168455/1152921504606846976)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((188314100459/147573952589676412928), (-47571799365/73786976294838206464)), (43/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-157412760817/4722366482869645213696), (49469490767/2361183241434822606848)), (53/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((272868082949/302231454903657293676544), (-26164782463/37778931862957161709568)), (65/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-241794217319/9671406556917033397649408), (112064299875/4835703278458516698824704)), (79/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((13547398135/19342813113834066795298816), (-242098040005/309485009821345068724781056)), (53/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-24351015173/1237940039285380274899124224), (131579900259/4951760157141521099596496896)), (17/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((86962826739/158456325028528675187087900672), (-287325445765/316912650057057350374175801344)), (339/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-79619342811/72057594037927936), (88500448179/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 1 => ⟨((69068908931/576460752303423488), (-104431681953/2305843009213693952)), (3/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-316581664795/36893488147419103232), (153608586945/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 3 => ⟨((37408279141/73786976294838206464), (-90121158823/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-251783514189/9444732965739290427392), (184523261073/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((48809570241/37778931862957161709568), (-43051110463/37778931862957161709568)), (1/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-35523966575/604462909807314587353088), (150207671421/2417851639229258349412352)), (1/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((196011789201/77371252455336267181195264), (-248784863081/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-32160882555/309485009821345068724781056), (24707742135/154742504910672534362390528)), (3/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((160589068423/39614081257132168796771975168), (-303549740341/39614081257132168796771975168)), (21/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-94747723741/633825300114114700748351602688), (226458699113/633825300114114700748351602688)), (17/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((104091492311/20282409603651670423947251286016), (-329589363861/20282409603651670423947251286016)), (27/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-51378883415/324518553658426726783156020576256), (234648534761/324518553658426726783156020576256)), (21/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358769297811/17179869184), (53229683379/17179869184)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((175917820671/137438953472), (3222643969/68719476736)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((338434253791/35184372088832), (-7954949511/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-275205578053/2251799813685248), (26092632595/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((166245276799/72057594037927936), (-93705551/140737488355328)), (21/144115188075855872), by norm_num⟩
  | 5 => ⟨((-238633812755/4611686018427387904), (93775418557/4611686018427387904)), (33/4611686018427387904), by norm_num⟩
  | 6 => ⟨((5884544613/4611686018427387904), (-95134430781/147573952589676412928)), (11/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-157400797207/4722366482869645213696), (98923796911/4722366482869645213696)), (107/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((272836675837/302231454903657293676544), (-209270002395/302231454903657293676544)), (131/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-241755011003/9671406556917033397649408), (224054490927/9671406556917033397649408)), (159/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((216712106623/309485009821345068724781056), (-60496866117/77371252455336267181195264)), (213/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-48689323865/2475880078570760549798248448), (262998868211/9903520314283042199192993792)), (273/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((173875478787/316912650057057350374175801344), (-287096296805/316912650057057350374175801344)), (85/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((241205077939/147573952589676412928), (-117035113863/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-85504638037/295147905179352825856), (205991220167/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((71938146911/2361183241434822606848), (-210883726941/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-92970609983/37778931862957161709568), (2562566099/1180591620717411303424)), (3/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((202994094715/1208925819614629174706176), (-6705699617/37778931862957161709568)), (5/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-196011789201/19342813113834066795298816), (124392431541/9671406556917033397649408)), (13/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((10720294185/19342813113834066795298816), (-263549249441/309485009821345068724781056)), (7/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((-68823886467/2475880078570760549798248448), (32523186465/618970019642690137449562112)), (1/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((50757709147/39614081257132168796771975168), (-242634320479/79228162514264337593543950336)), (1/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-68155143775/1267650600228229401496703205376), (215802559671/1267650600228229401496703205376)), (1/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((80738245365/40564819207303340847894502572032), (-368733411767/40564819207303340847894502572032)), (15/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-38291704381/649037107316853453566312041152512), (76055048343/162259276829213363391578010288128)), (7/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((1061012191/1298074214633706907132624082305024), (-243386959469/10384593717069655257060992658440192)), (3/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358769297839/17179869184), (53229683365/17179869184)), (9/17179869184), by norm_num⟩
  | 1 => ⟨((175917820631/137438953472), (3222643981/68719476736)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((338434254863/35184372088832), (-15909899415/17592186044416)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-137602791797/1125899906842624), (26092635039/1125899906842624)), (7/2251799813685248), by norm_num⟩
  | 4 => ⟨((332490577797/144115188075855872), (-23988627451/36028797018963968)), (11/72057594037927936), by norm_num⟩
  | 5 => ⟨((-7457308109/144115188075855872), (5860967367/288230376151711744)), (17/2305843009213693952), by norm_num⟩
  | 6 => ⟨((188305509405/147573952589676412928), (-95134556451/147573952589676412928)), (45/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-78700464239/2361183241434822606848), (98924045043/4722366482869645213696)), (27/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((17052316443/18889465931478580854784), (-209270927971/302231454903657293676544)), (33/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-241755530985/9671406556917033397649408), (112028068685/4835703278458516698824704)), (5/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((216712722607/309485009821345068724781056), (-241990277681/309485009821345068724781056)), (107/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-194757879745/9903520314283042199192993792), (263003510243/9903520314283042199192993792)), (137/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((173875737823/316912650057057350374175801344), (-143551862193/158456325028528675187087900672)), (341/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-57550517529/9444732965739290427392), (168706981553/37778931862957161709568)), (1/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((223129463959/151115727451828646838272), (-98402538201/75557863725914323419136)), (9/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((-121796456829/604462909807314587353088), (64374716323/302231454903657293676544)), (11/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((196011789201/9671406556917033397649408), (-124392431541/4835703278458516698824704)), (3/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((-32160882555/19342813113834066795298816), (24707742135/9671406556917033397649408)), (5/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((144530161581/1237940039285380274899124224), (-136597383153/618970019642690137449562112)), (1/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((-142121585613/19807040628566084398385987584), (339688048669/19807040628566084398385987584)), (11/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((122679258795/316912650057057350374175801344), (-24277787963/19807040628566084398385987584)), (7/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((-22707631509/1267650600228229401496703205376), (207412544119/2535301200456458802993406410752)), (31/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((13162773381/20282409603651670423947251286016), (-209151382943/40564819207303340847894502572032)), (35/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((-7002680461/649037107316853453566312041152512), (401588483123/1298074214633706907132624082305024)), (19/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((-20516427591/20769187434139310514121985316880384), (-184681638623/10384593717069655257060992658440192)), (39/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((3002229215/20769187434139310514121985316880384), (327039522097/332306998946228968225951765070086144)), (39/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358769297839/17179869184), (53229683365/17179869184)), (5/8589934592), by norm_num⟩
  | 1 => ⟨((175917820631/137438953472), (3222643981/68719476736)), (3/137438953472), by norm_num⟩
  | 2 => ⟨((42304281857/4398046511104), (-31819798823/35184372088832)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-68801395887/562949953421312), (13046317505/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((332490577557/144115188075855872), (-23988627359/36028797018963968)), (23/144115188075855872), by norm_num⟩
  | 5 => ⟨((-119316929475/2305843009213693952), (46887738427/2305843009213693952)), (35/4611686018427387904), by norm_num⟩
  | 6 => ⟨((94152754173/73786976294838206464), (-1486477405/2305843009213693952)), (23/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-78700463325/2361183241434822606848), (197848078509/9444732965739290427392)), (109/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((136418528837/151115727451828646838272), (-209270903245/302231454903657293676544)), (133/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-241755524709/9671406556917033397649408), (14003505469/604462909807314587353088)), (161/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((54178179817/77371252455336267181195264), (-241990181935/309485009821345068724781056)), (215/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-24344736191/1237940039285380274899124224), (263003334117/9903520314283042199192993792)), (275/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((173875783633/316912650057057350374175801344), (-287103412497/316912650057057350374175801344)), (171/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((98421379255/2417851639229258349412352), (-104039945573/2417851639229258349412352)), (3/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((-118795023759/9671406556917033397649408), (150778704897/9671406556917033397649408)), (1/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((155931551783/77371252455336267181195264), (-59897556691/19342813113834066795298816)), (13/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((-72995031101/309485009821345068724781056), (34494288675/77371252455336267181195264)), (1/38685626227668133590597632), by norm_num⟩
  | 4 => ⟨((6729241743/309485009821345068724781056), (-257339430811/4951760157141521099596496896)), (1/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((-65057182695/39614081257132168796771975168), (411986704825/79228162514264337593543950336)), (27/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((64223604269/633825300114114700748351602688), (-146655334225/316912650057057350374175801344)), (21/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((-47864630477/10141204801825835211973625643008), (190137620857/5070602400912917605986812821504)), (15/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((15915182865/162259276829213363391578010288128), (-114087637251/40564819207303340847894502572032)), (5/20282409603651670423947251286016), by norm_num⟩
  | 9 => ⟨((28495038321/2596148429267413814265248164610048), (256502275865/1298074214633706907132624082305024)), (51/2596148429267413814265248164610048), by norm_num⟩
  | 10 => ⟨((-20014861433/10384593717069655257060992658440192), (-272532935081/20769187434139310514121985316880384)), (15/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((8290029471/41538374868278621028243970633760768), (137777501877/166153499473114484112975882535043072)), (35/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((-11282396783/664613997892457936451903530140172288), (-266519475357/5316911983139663491615228241121378304)), (19/2658455991569831745807614120560689152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358769297839/17179869184), (53229683365/17179869184)), (11/17179869184), by norm_num⟩
  | 1 => ⟨((175917820631/137438953472), (3222643981/68719476736)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((42304281857/4398046511104), (-31819798823/35184372088832)), (5/35184372088832), by norm_num⟩
  | 3 => ⟨((-275205583549/2251799813685248), (52185270021/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 4 => ⟨((41561322195/18014398509481984), (-95954509443/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((-119316929479/2305843009213693952), (46887738439/2305843009213693952)), (9/1152921504606846976), by norm_num⟩
  | 6 => ⟨((188305508361/147573952589676412928), (-23783638497/36893488147419103232)), (47/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-314801853345/9444732965739290427392), (197848078863/9444732965739290427392)), (55/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((34104632213/37778931862957161709568), (-209270904095/302231454903657293676544)), (67/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-241755524603/9671406556917033397649408), (224056089415/9671406556917033397649408)), (81/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((13544544917/19342813113834066795298816), (-60497546499/77371252455336267181195264)), (27/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-3043091993/154742504910672534362390528), (263003342329/9903520314283042199192993792)), (69/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((173875778253/316912650057057350374175801344), (-287103428383/316912650057057350374175801344)), (343/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-126298845165/309485009821345068724781056), (24257413435/38685626227668133590597632)), (7/154742504910672534362390528), by norm_num⟩
  | 1 => ⟨((177369904145/1237940039285380274899124224), (-335269323595/1237940039285380274899124224)), (11/618970019642690137449562112), by norm_num⟩
  | 2 => ⟨((-32702635917/1237940039285380274899124224), (312653268905/4951760157141521099596496896)), (21/4951760157141521099596496896), by norm_num⟩
  | 3 => ⟨((131734837339/39614081257132168796771975168), (-52139709347/4951760157141521099596496896)), (31/39614081257132168796771975168), by norm_num⟩
  | 4 => ⟨((-48767594011/158456325028528675187087900672), (222722716373/158456325028528675187087900672)), (1/9903520314283042199192993792), by norm_num⟩
  | 5 => ⟨((12720946023/633825300114114700748351602688), (-404261833885/2535301200456458802993406410752)), (1/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((-5639687877/10141204801825835211973625643008), (161711912493/10141204801825835211973625643008)), (7/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((-12982464711/162259276829213363391578010288128), (-467454257467/324518553658426726783156020576256)), (11/81129638414606681695789005144064), by norm_num⟩
  | 8 => ⟨((5699286779/324518553658426726783156020576256), (310418007925/2596148429267413814265248164610048)), (35/2596148429267413814265248164610048), by norm_num⟩
  | 9 => ⟨((-92326027853/41538374868278621028243970633760768), (-191803441715/20769187434139310514121985316880384)), (47/41538374868278621028243970633760768), by norm_num⟩
  | 10 => ⟨((75391206987/332306998946228968225951765070086144), (27827122695/41538374868278621028243970633760768)), (1/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((-27057403807/1329227995784915872903807060280344576), (-244398100303/5316911983139663491615228241121378304)), (39/5316911983139663491615228241121378304), by norm_num⟩
  | 12 => ⟨((35449397201/21267647932558653966460912964485513216), (255154143855/85070591730234615865843651857942052864)), (47/85070591730234615865843651857942052864), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358769297839/17179869184), (53229683365/17179869184)), (3/4294967296), by norm_num⟩
  | 1 => ⟨((175917820631/137438953472), (3222643981/68719476736)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((42304281857/4398046511104), (-31819798823/35184372088832)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-275205583549/2251799813685248), (52185270021/2251799813685248)), (5/1125899906842624), by norm_num⟩
  | 4 => ⟨((41561322195/18014398509481984), (-95954509443/144115188075855872)), (25/144115188075855872), by norm_num⟩
  | 5 => ⟨((-119316929479/2305843009213693952), (93775476877/4611686018427387904)), (37/4611686018427387904), by norm_num⟩
  | 6 => ⟨((188305508361/147573952589676412928), (-47567276993/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-157400926673/4722366482869645213696), (197848078849/9444732965739290427392)), (111/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((272837057709/302231454903657293676544), (-209270904059/302231454903657293676544)), (135/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-15109720289/604462909807314587353088), (112028044663/4835703278458516698824704)), (163/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((108356359371/154742504910672534362390528), (-241990185789/309485009821345068724781056)), (217/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-97378943877/4951760157141521099596496896), (131501670937/4951760157141521099596496896)), (277/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((173875778781/316912650057057350374175801344), (-35887928429/39614081257132168796771975168)), (43/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1229189111428731/1048576), (53155324366673/1048576)), (1139145/524288), by norm_num⟩
  | 1 => ⟨((-384721358767/256), (2537509819/256)), (187/64), by norm_num⟩
  | 2 => ⟨((-249150355933/256), (-7000682927/256)), (1017/512), by norm_num⟩
  | 3 => ⟨((-434485721783/1024), (-26567569521/1024)), (233/256), by norm_num⟩
  | 4 => ⟨((-286776747575/2048), (-26612170955/2048)), (649/2048), by norm_num⟩
  | 5 => ⟨((-305539221357/8192), (-18828703169/4096)), (731/8192), by norm_num⟩
  | 6 => ⟨((-136785809585/16384), (-5220636555/4096)), (693/32768), by norm_num⟩
  | 7 => ⟨((-211656971857/131072), (-38349226051/131072)), (1139/262144), by norm_num⟩
  | 8 => ⟨((-72198978109/262144), (-60336394913/1048576)), (829/1048576), by norm_num⟩
  | 9 => ⟨((-352875669095/8388608), (-83271474545/8388608)), (1083/8388608), by norm_num⟩
  | 10 => ⟨((-97709207241/16777216), (-102570405751/67108864)), (161/8388608), by norm_num⟩
  | 11 => ⟨((-396243299771/536870912), (-114265850057/536870912)), (11/4194304), by norm_num⟩
  | 12 => ⟨((-185348035589/2147483648), (-116342860611/4294967296)), (713/2147483648), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1611178364647321/10141204801825835211973625643008), (4035979841599/10141204801825835211973625643008)), (911/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((113426148223215/39614081257132168796771975168), (4957342971953/633825300114114700748351602688)), (281/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1930341847681859/39614081257132168796771975168), (1398074541341/9903520314283042199192993792)), (1269/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1932695874511703/2475880078570760549798248448), (5954793222395/2475880078570760549798248448)), (1351/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1814408657811805/154742504910672534362390528), (5969308541823/154742504910672534362390528)), (1355/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1590119814645527/9671406556917033397649408), (5611696166407/9671406556917033397649408)), (637/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1294333932273065/604462909807314587353088), (2462879778571/302231454903657293676544)), (1119/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1945646430284891/75557863725914323419136), (4016794530407/37778931862957161709568)), (913/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1341012176911205/4722366482869645213696), (6050888062577/4722366482869645213696)), (1377/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1681356720141897/590295810358705651712), (8361954135933/590295810358705651712)), (1903/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1898561611690167/73786976294838206464), (10515816285383/73786976294838206464)), (2395/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1907407788831687/9223372036854775808), (11918085131597/9223372036854775808)), (2717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((419751462072681/288230376151711744), (3007203181417/288230376151711744)), (1373/576460752303423488), by norm_num⟩
  | 5 => ⟨((1269369302152439/144115188075855872), (10651151384073/144115188075855872)), (2437/144115188075855872), by norm_num⟩
  | 4 => ⟨((1604619376849919/36028797018963968), (8116038785609/18014398509481984)), (1861/18014398509481984), by norm_num⟩
  | 3 => ⟨((101993734559905/562949953421312), (20744881208829/9007199254740992)), (1193/2251799813685248), by norm_num⟩
  | 2 => ⟨((1258770553748919/2251799813685248), (10721593480235/1125899906842624)), (4957/2251799813685248), by norm_num⟩
  | 1 => ⟨((332687124253815/281474976710656), (33968315226265/1125899906842624)), (1979/281474976710656), by norm_num⟩
  | 0 => ⟨((779238516995935/562949953421312), (37754084467939/562949953421312)), (8931/562949953421312), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((779238516995935/562949953421312), (37754084467939/562949953421312)), (34069063426780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((538047202770297/281474976710656), (52259417755593/281474976710656)), (25923/562949953421312), by norm_num⟩
  | 2 => ⟨((509394740903679/140737488355328), (199790644769857/281474976710656)), (54367/281474976710656), by norm_num⟩
  | 3 => ⟨((886416013038405/70368744177664), (45195981946975/8796093022208)), (58843/35184372088832), by norm_num⟩
  | 4 => ⟨((36359916965335/274877906944), (569321544543205/4398046511104)), (260895/4398046511104), by norm_num⟩
  | 5 => ⟨((12715278359829/17179869184), (1176686287531493/34359738368)), (133365/4294967296), by norm_num⟩
  | 6 => ⟨((-1229189111428731/1048576), (53155324366673/1048576)), (1139145/524288), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((358769297839/17179869184), (53229683365/17179869184)), (3/4294967296), by norm_num⟩, 0, gammaExpValuePoly, gammaExpValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem gammaExpValue_checks : CertifiedScalarExp.Checks gammaExpValue := by
  constructor
  · norm_num [gammaExpValue, CertifiedScalarExp.reduced, gammaExpValuePoly, gammaExpValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        gammaExpValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue, gammaExpValueSquares, gammaExpValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, gammaExpValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_gammaExp : Sound J_gammaExp F_gammaExp c := by
  apply exp_sound (A_mainCorr6 hcre) S_mainCorr6 gammaExpValue gammaExpValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue,J_mainCorr6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaExp,J_mainCorr6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((204800/500291), (-180480/500291)), 0, by norm_num⟩
  | 1 => ⟨((-4685004800/250291084681), (36962304000/250291084681)), 0, by norm_num⟩
  | 2 => ⟨((-2855733821440000/125218377046142171), (-4207714762752000/125218377046142171)), 0, by norm_num⟩
  | 3 => ⟨((188748358701/17592186044416), (48629311767/17592186044416)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-189618770075/70368744177664), (24091999185/17592186044416)), (1/35184372088832), by norm_num⟩
  | 5 => ⟨((21428956407/70368744177664), (-215708702957/281474976710656)), (1/70368744177664), by norm_num⟩
  | 6 => ⟨((85456286925/1125899906842624), (238449760539/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 7 => ⟨((-60501648385/1125899906842624), (-33391926193/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 8 => ⟨((36813199575/2251799813685248), (-65252759153/18014398509481984)), (5/4503599627370496), by norm_num⟩
  | 9 => ⟨((-48509695569/18014398509481984), (265909781103/72057594037927936)), (1/2251799813685248), by norm_num⟩
  | 10 => ⟨((-32989818659/288230376151711744), (-357705585729/288230376151711744)), (25/144115188075855872), by norm_num⟩
  | 11 => ⟨((142547075549/576460752303423488), (67264953283/288230376151711744)), (5/72057594037927936), by norm_num⟩
  | 12 => ⟨((-427539960619/4611686018427387904), (-14590137897/4611686018427387904)), (31/1152921504606846976), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (1551/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (1551/1280)))⁻¹=value ((204800/500291), (-180480/500291)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((204800/500291), (-180480/500291))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_gammaFactor1 : Sound J_gammaFactor1 F_gammaFactor1 c := by
  apply sound_round (sound_add (A_base hcre) (A_q0 hcre) S_base S_q0)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor1, J_base, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3891200/11647201), (-1985280/11647201)), 0, by norm_num⟩
  | 1 => ⟨((-5600050380800/135657291134401), (7725121536000/135657291134401)), 0, by norm_num⟩
  | 2 => ⟨((35931892209/17592186044416), (-458476174311/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((54138949041/70368744177664), (41355262595/17592186044416)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-92566889059/281474976710656), (-184149107923/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((372958309345/4503599627370496), (119863518017/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-145032099847/9007199254740992), (23526145987/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 7 => ⟨((22221773275/9007199254740992), (-130322904687/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 8 => ⟨((-1161833477/4503599627370496), (295365048855/576460752303423488)), (19/576460752303423488), by norm_num⟩
  | 9 => ⟨((-2645697177/4611686018427387904), (-248053548325/2305843009213693952)), (39/4611686018427387904), by norm_num⟩
  | 10 => ⟨((85445973989/9223372036854775808), (82646443759/4611686018427387904)), (5/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-226883708015/73786976294838206464), (-40658137579/18446744073709551616)), (21/36893488147419103232), by norm_num⟩
  | 12 => ⟨((207040478501/295147905179352825856), (15661109647/147573952589676412928)), (43/295147905179352825856), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (1551/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (1551/1280)))⁻¹=value ((3891200/11647201), (-1985280/11647201)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/11647201), (-1985280/11647201))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((438614425600/5826989835491), (-1108869120000/5826989835491)), 0, by norm_num⟩
  | 1 => ⟨((99231542731/4398046511104), (49880118219/549755813888)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-109284945225/4398046511104), (-45239046343/2199023255552)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((350427242881/35184372088832), (1818512293/4398046511104)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-83238523905/35184372088832), (59693317615/35184372088832)), (3/70368744177664), by norm_num⟩
  | 5 => ⟨((31202965647/140737488355328), (-223200172833/281474976710656)), (5/281474976710656), by norm_num⟩
  | 6 => ⟨((51792649703/562949953421312), (117754496145/562949953421312)), (1/140737488355328), by norm_num⟩
  | 7 => ⟨((-253117480177/4503599627370496), (-125422523229/4503599627370496)), (13/4503599627370496), by norm_num⟩
  | 8 => ⟨((74788232627/4503599627370496), (-37241458465/9007199254740992)), (21/18014398509481984), by norm_num⟩
  | 9 => ⟨((-193997443257/72057594037927936), (34207681811/9007199254740992)), (33/72057594037927936), by norm_num⟩
  | 10 => ⟨((-17830002673/144115188075855872), (-22679436779/18014398509481984)), (51/288230376151711744), by norm_num⟩
  | 11 => ⟨((72159802259/288230376151711744), (135800473365/576460752303423488)), (41/576460752303423488), by norm_num⟩
  | 12 => ⟨((-13461717753/144115188075855872), (-15079547573/4611686018427387904)), (31/1152921504606846976), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct1 : Sound J_gammaProduct1 F_gammaProduct1 c := by
  apply sound_round (sound_mul (A_gammaInverse0 hcre) (A_gammaInverse1 hcre) S_gammaInverse0 S_gammaInverse1)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct1, J_gammaInverse0, J_gammaInverse1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(2, 0), 0, by norm_num⟩
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

theorem S_q3 : Sound J_q3 F_q3 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (2, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((27/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_gammaFactor2 : Sound J_gammaFactor2 F_gammaFactor2 c := by
  apply sound_round (sound_add (A_base hcre) (A_q3 hcre) S_base S_q3)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor2, J_base, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((614400/2340889), (-661760/7022667)), 0, by norm_num⟩
  | 1 => ⟨((-1479729971200/49317851792889), (135528448000/5479761310321)), 0, by norm_num⟩
  | 2 => ⟨((97537569353/35184372088832), (-327874162979/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-81216147409/562949953421312), (104437613373/140737488355328)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-72196467353/4503599627370496), (-234595555673/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((7895227669/1125899906842624), (232685480373/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((-220327509035/144115188075855872), (-98335844097/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((305443570673/1152921504606846976), (61714822389/576460752303423488)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-45899541527/1152921504606846976), (-1806662905/1152921504606846976)), (17/9223372036854775808), by norm_num⟩
  | 9 => ⟨((390951698261/73786976294838206464), (-15404084821/9223372036854775808)), (25/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-181996871805/295147905179352825856), (34592176233/73786976294838206464)), (19/295147905179352825856), by norm_num⟩
  | 11 => ⟨((34728937017/590295810358705651712), (-106933575753/1180591620717411303424)), (7/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-65229224543/18889465931478580854784), (34611410387/2361183241434822606848)), (41/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (1551/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (1551/1280)))⁻¹=value ((614400/2340889), (-661760/7022667)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/2340889), (-661760/7022667))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8022999781/4398046511104), (-250863571093/4398046511104)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((37206993983/2199023255552), (128682639057/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-26518930527/2199023255552), (-53660706083/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((318281759147/70368744177664), (-42053023503/70368744177664)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-144463395347/140737488355328), (67537081303/70368744177664)), (1/35184372088832), by norm_num⟩
  | 5 => ⟨((41069843877/562949953421312), (-113527966039/281474976710656)), (3/281474976710656), by norm_num⟩
  | 6 => ⟨((59996501611/1125899906842624), (115515863239/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 7 => ⟨((-263035227867/9007199254740992), (-29198798659/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 8 => ⟨((303083084079/36028797018963968), (-83741303815/36028797018963968)), (25/36028797018963968), by norm_num⟩
  | 9 => ⟨((-193574315471/144115188075855872), (281292783461/144115188075855872)), (39/144115188075855872), by norm_num⟩
  | 10 => ⟨((-19253961677/288230376151711744), (-367901265511/576460752303423488)), (15/144115188075855872), by norm_num⟩
  | 11 => ⟨((146126048465/1152921504606846976), (17127353313/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 12 => ⟨((-108506475169/2305843009213693952), (-7750678419/4611686018427387904)), (9/576460752303423488), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct2 : Sound J_gammaProduct2 F_gammaProduct2 c := by
  apply sound_round (sound_mul (A_gammaProduct1 hcre) (A_gammaInverse2 hcre) S_gammaProduct1 S_gammaInverse2)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct2, J_gammaProduct1, J_gammaInverse2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(3, 0), 0, by norm_num⟩
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

theorem S_q4 : Sound J_q4 F_q4 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (3, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((35/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_gammaFactor3 : Sound J_gammaFactor3 F_gammaFactor3 c := by
  apply sound_round (sound_add (A_base hcre) (A_q4 hcre) S_base S_q4)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor3, J_base, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7168000/33765601), (-1985280/33765601)), 0, by norm_num⟩
  | 1 => ⟨((-23719443660800/1140115810891201), (14230487040000/1140115810891201)), 0, by norm_num⟩
  | 2 => ⟨((129571375935/70368744177664), (-34066392313/17592186044416)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-155955716797/1125899906842624), (146182745169/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((63669912743/9007199254740992), (-142469941535/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((12948031521/72057594037927936), (513860644439/144115188075855872)), (9/144115188075855872), by norm_num⟩
  | 6 => ⟨((-35710314769/288230376151711744), (-215126759527/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((108633803/4503599627370496), (20734691867/576460752303423488)), (1/576460752303423488), by norm_num⟩
  | 8 => ⟨((-133471806749/36893488147419103232), (-229385073787/73786976294838206464)), (9/36893488147419103232), by norm_num⟩
  | 9 => ⟨((280622331685/590295810358705651712), (132001132383/590295810358705651712)), (5/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-269334472277/4722366482869645213696), (-46090719875/4722366482869645213696)), (23/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((239544675261/37778931862957161709568), (-48410466275/75557863725914323419136)), (51/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-98858128841/151115727451828646838272), (153781681903/604462909807314587353088)), (7/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (1551/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (1551/1280)))⁻¹=value ((7168000/33765601), (-1985280/33765601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/33765601), (-1985280/33765601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-52186314467/17592186044416), (-429814467949/35184372088832)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((6581852729/1099511627776), (56523257535/8796093022208)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((-263393370181/70368744177664), (-76850284235/70368744177664)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((381245176467/281474976710656), (-54454109053/140737488355328)), (7/281474976710656), by norm_num⟩
  | 4 => ⟨((-82716822587/281474976710656), (48552223901/140737488355328)), (7/562949953421312), by norm_num⟩
  | 5 => ⟨((7218995043/562949953421312), (-76093204921/562949953421312)), (11/2251799813685248), by norm_num⟩
  | 6 => ⟨((179758522389/9007199254740992), (150292088369/4503599627370496)), (17/9007199254740992), by norm_num⟩
  | 7 => ⟨((-181245646941/18014398509481984), (-143796945031/36028797018963968)), (13/18014398509481984), by norm_num⟩
  | 8 => ⟨((408481638793/144115188075855872), (-123962556789/144115188075855872)), (5/18014398509481984), by norm_num⟩
  | 9 => ⟨((-128535769715/288230376151711744), (48131275767/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 10 => ⟨((-27678089207/1152921504606846976), (-248529069143/1152921504606846976)), (3/72057594037927936), by norm_num⟩
  | 11 => ⟨((49320917409/1152921504606846976), (23030889221/576460752303423488)), (19/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-72881623575/4611686018427387904), (-5285579651/9223372036854775808)), (115/18446744073709551616), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct3 : Sound J_gammaProduct3 F_gammaProduct3 c := by
  apply sound_round (sound_mul (A_gammaProduct2 hcre) (A_gammaInverse3 hcre) S_gammaProduct2 S_gammaInverse3)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct3, J_gammaProduct2, J_gammaInverse3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(4, 0), 0, by norm_num⟩
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

theorem S_q5 : Sound J_q5 F_q5 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (4, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((43/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_gammaFactor4 : Sound J_gammaFactor4 F_gammaFactor4 c := by
  apply sound_round (sound_add (A_base hcre) (A_q5 hcre) S_base S_q5)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor4, J_base, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8806400/49740001), (-1985280/49740001)), 0, by norm_num⟩
  | 1 => ⟨((-36805672140800/2474067699480001), (17483169792000/2474067699480001)), 0, by norm_num⟩
  | 2 => ⟨((165495311405/140737488355328), (-64911567351/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-24119071439/281474976710656), (236723595605/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((24713608387/4503599627370496), (-6201617169/562949953421312)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((-9581209991/36028797018963968), (39081205805/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((8735126681/4611686018427387904), (-58413527635/576460752303423488)), (15/4611686018427387904), by norm_num⟩
  | 7 => ⟨((68420798427/36893488147419103232), (332339743251/36893488147419103232)), (7/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-101514140681/295147905179352825856), (-7013676659/9223372036854775808)), (13/295147905179352825856), by norm_num⟩
  | 9 => ⟨((13465477337/295147905179352825856), (71369268969/1180591620717411303424)), (23/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-99078003763/18889465931478580854784), (-167776549537/37778931862957161709568)), (21/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((334237949523/604462909807314587353088), (43591163065/151115727451828646838272)), (19/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-264543278599/4835703278458516698824704), (-35061075179/2417851639229258349412352)), (17/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (1551/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (1551/1280)))⁻¹=value ((8806400/49740001), (-1985280/49740001)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/49740001), (-1985280/49740001))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-71268562555/70368744177664), (-287728923671/140737488355328)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((203615865615/140737488355328), (37279600941/35184372088832)), (1/35184372088832), by norm_num⟩
  | 2 => ⟨((-240804807651/281474976710656), (-7661946055/70368744177664)), (9/562949953421312), by norm_num⟩
  | 3 => ⟨((42540390785/140737488355328), (-146365249703/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 4 => ⟨((-140565112629/2251799813685248), (12715421101/140737488355328)), (9/2251799813685248), by norm_num⟩
  | 5 => ⟨((2694615733/4503599627370496), (-303426044053/9007199254740992)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((197606121507/36028797018963968), (146022860699/18014398509481984)), (21/36028797018963968), by norm_num⟩
  | 7 => ⟨((-372956652621/144115188075855872), (-32900495535/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 8 => ⟨((412061788539/576460752303423488), (-68088303089/288230376151711744)), (3/36028797018963968), by norm_num⟩
  | 9 => ⟨((-63905476249/576460752303423488), (197422873683/1152921504606846976)), (19/576460752303423488), by norm_num⟩
  | 10 => ⟨((-7445451609/1152921504606846976), (-251697646637/4611686018427387904)), (29/2305843009213693952), by norm_num⟩
  | 11 => ⟨((24971063233/2305843009213693952), (11608377955/1152921504606846976)), (89/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-293709150529/73786976294838206464), (-5382311351/36893488147419103232)), (17/9223372036854775808), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct4 : Sound J_gammaProduct4 F_gammaProduct4 c := by
  apply sound_round (sound_mul (A_gammaProduct3 hcre) (A_gammaInverse4 hcre) S_gammaProduct3 S_gammaInverse4)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct4, J_gammaProduct3, J_gammaInverse4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(5, 0), 0, by norm_num⟩
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

theorem S_q6 : Sound J_q6 F_q6 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (5, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((51/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_gammaFactor5 : Sound J_gammaFactor5 F_gammaFactor5 c := by
  apply sound_round (sound_add (A_base hcre) (A_q6 hcre) S_base S_q6)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor5, J_base, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3481600/22997067), (-661760/22997067)), 0, by norm_num⟩
  | 1 => ⟨((-1947268710400/176288363534163), (2303983616000/528865090602489)), 0, by norm_num⟩
  | 2 => ⟨((108854655013/140737488355328), (-68778098579/140737488355328)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-232011341187/4503599627370496), (216718756015/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((115554715129/36028797018963968), (-315888576951/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((-51796880681/288230376151711744), (108947514575/288230376151711744)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((75306237989/9223372036854775808), (-287750621767/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-24964695445/147573952589676412928), (182921973623/73786976294838206464)), (13/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-26991930209/1180591620717411303424), (-448837383859/2361183241434822606848)), (5/590295810358705651712), by norm_num⟩
  | 9 => ⟨((42176929395/9444732965739290427392), (265590020879/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-81652716319/151115727451828646838272), (-75562349503/75557863725914323419136)), (3/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((33420816485/604462909807314587353088), (164237030925/2417851639229258349412352)), (9/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-199718392361/38685626227668133590597632), (-168140192417/38685626227668133590597632)), (27/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (1551/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (1551/1280)))⁻¹=value ((3481600/22997067), (-661760/22997067)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/22997067), (-661760/22997067))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-119435186637/562949953421312), (-157834327785/562949953421312)), (3/562949953421312), by norm_num⟩
  | 1 => ⟨((303560046651/1125899906842624), (9636785859/70368744177664)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((-349098885393/2251799813685248), (3708049809/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((241987821995/4503599627370496), (-138414153695/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 4 => ⟨((-5897334057/562949953421312), (167299712657/9007199254740992)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((-12720045307/36028797018963968), (-240453409275/36028797018963968)), (27/72057594037927936), by norm_num⟩
  | 6 => ⟨((170970311677/144115188075855872), (226183807339/144115188075855872)), (21/144115188075855872), by norm_num⟩
  | 7 => ⟨((-152892508093/288230376151711744), (-2981618165/18014398509481984)), (31/576460752303423488), by norm_num⟩
  | 8 => ⟨((82984430077/576460752303423488), (-29650902811/576460752303423488)), (23/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-203030016529/9223372036854775808), (323545959183/9223372036854775808)), (71/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-12789621305/9223372036854775808), (-203818305545/18446744073709551616)), (109/36893488147419103232), by norm_num⟩
  | 11 => ⟨((40457034787/18446744073709551616), (74861381155/36893488147419103232)), (83/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-236717502701/295147905179352825856), (-8732388855/295147905179352825856)), (253/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct5 : Sound J_gammaProduct5 F_gammaProduct5 c := by
  apply sound_round (sound_mul (A_gammaProduct4 hcre) (A_gammaInverse5 hcre) S_gammaProduct4 S_gammaInverse5)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct5, J_gammaProduct4, J_gammaInverse5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(6, 0), 0, by norm_num⟩
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

theorem S_q7 : Sound J_q7 F_q7 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (6, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((59/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_gammaFactor6 : Sound J_gammaFactor6 F_gammaFactor6 c := by
  apply sound_round (sound_add (A_base hcre) (A_q7 hcre) S_base S_q7)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor6, J_base, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12083200/91519201), (-1985280/91519201)), 0, by norm_num⟩
  | 1 => ⟨((-71031192780800/8375764151678401), (23988535296000/8375764151678401)), 0, by norm_num⟩
  | 2 => ⟨((297674721861/562949953421312), (-39554373849/140737488355328)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-286956803299/9007199254740992), (218773003683/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((132563691279/72057594037927936), (-280873742379/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-57823366829/576460752303423488), (171339157297/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 6 => ⟨((92415702793/18446744073709551616), (-12565212697/1152921504606846976)), (5/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-62723447297/295147905179352825856), (228386495237/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 8 => ⟨((207940529/36893488147419103232), (-126057189013/2361183241434822606848)), (5/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((488713009/2361183241434822606848), (270910532513/75557863725914323419136)), (13/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-31766020639/604462909807314587353088), (-283430683995/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((14536399083/2417851639229258349412352), (72085872995/4835703278458516698824704)), (11/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-43217429465/77371252455336267181195264), (-284376739987/309485009821345068724781056)), (7/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (1551/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (1551/1280)))⁻¹=value ((12083200/91519201), (-1985280/91519201)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/91519201), (-1985280/91519201))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-76770975369/2251799813685248), (-145983045649/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 1 => ⟨((370826765621/9007199254740992), (63061280725/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 2 => ⟨((-52472764229/2251799813685248), (6986435513/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 3 => ⟨((285786172781/36028797018963968), (-204677583419/36028797018963968)), (7/18014398509481984), by norm_num⟩
  | 4 => ⟨((-811892839/562949953421312), (113152533153/36028797018963968)), (13/72057594037927936), by norm_num⟩
  | 5 => ⟨((-9385079589/72057594037927936), (-9876055505/9007199254740992)), (21/288230376151711744), by norm_num⟩
  | 6 => ⟨((243460371693/1152921504606846976), (36381907013/144115188075855872)), (33/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-52056641581/576460752303423488), (-114004161779/4611686018427387904)), (49/4611686018427387904), by norm_num⟩
  | 8 => ⟨((222467530213/9223372036854775808), (-1334699917/144115188075855872)), (37/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-134187828269/36893488147419103232), (220694689307/36893488147419103232)), (55/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-36529698855/147573952589676412928), (-137469295047/73786976294838206464)), (21/36893488147419103232), by norm_num⟩
  | 11 => ⟨((218485282611/590295810358705651712), (12567089535/36893488147419103232)), (127/590295810358705651712), by norm_num⟩
  | 12 => ⟨((-317960666929/2361183241434822606848), (-11759603265/2361183241434822606848)), (97/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct6 : Sound J_gammaProduct6 F_gammaProduct6 c := by
  apply sound_round (sound_mul (A_gammaProduct5 hcre) (A_gammaInverse6 hcre) S_gammaProduct5 S_gammaInverse6)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct6, J_gammaProduct5, J_gammaInverse6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(7, 0), 0, by norm_num⟩
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

theorem S_q8 : Sound J_q8 F_q8 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (7, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((67/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_gammaFactor7 : Sound J_gammaFactor7 F_gammaFactor7 c := by
  apply sound_round (sound_add (A_base hcre) (A_q8 hcre) S_base S_q8)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor7, J_base, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13721600/117324001), (-1985280/117324001)), 0, by norm_num⟩
  | 1 => ⟨((-92170484940800/13764921210648001), (27241218048000/13764921210648001)), 0, by norm_num⟩
  | 2 => ⟨((211006599573/562949953421312), (-97042221899/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-184289124229/9007199254740992), (14920065111/1125899906842624)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((78134996167/72057594037927936), (-136625605597/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-63858519265/1152921504606846976), (37246626121/576460752303423488)), (3/1152921504606846976), by norm_num⟩
  | 6 => ⟨((49664252015/18446744073709551616), (-313373193221/73786976294838206464)), (7/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-143449486947/1180591620717411303424), (20006014767/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 8 => ⟨((90885125825/18889465931478580854784), (-318913086715/18889465931478580854784)), (9/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-20932036565/151115727451828646838272), (310690409085/302231454903657293676544)), (21/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-361097381/604462909807314587353088), (-148180470743/2417851639229258349412352)), (23/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((21410729779/38685626227668133590597632), (276895518381/77371252455336267181195264)), (25/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-605851139/9671406556917033397649408), (-63319302549/309485009821345068724781056)), (7/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (1551/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (1551/1280)))⁻¹=value ((13721600/117324001), (-1985280/117324001)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/117324001), (-1985280/117324001))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-163421528873/36028797018963968), (-115802201135/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 1 => ⟨((385105395545/72057594037927936), (78584270355/72057594037927936)), (13/72057594037927936), by norm_num⟩
  | 2 => ⟨((-107891926641/36028797018963968), (13305765439/18014398509481984)), (15/144115188075855872), by norm_num⟩
  | 3 => ⟨((288357741629/288230376151711744), (-7810728631/9007199254740992)), (9/144115188075855872), by norm_num⟩
  | 4 => ⟨((-24023496213/144115188075855872), (129959565961/288230376151711744)), (17/576460752303423488), by norm_num⟩
  | 5 => ⟨((-64224950897/2305843009213693952), (-1385394541/9007199254740992)), (27/2305843009213693952), by norm_num⟩
  | 6 => ⟨((147108335843/4611686018427387904), (160074996787/4611686018427387904)), (11/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-30296065349/2305843009213693952), (-28805024311/9223372036854775808)), (33/18446744073709551616), by norm_num⟩
  | 8 => ⟨((127613795483/36893488147419103232), (-104765411075/73786976294838206464)), (49/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-18978780913/36893488147419103232), (503513035/576460752303423488)), (9/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-22303642967/590295810358705651712), (-317737860757/1180591620717411303424)), (109/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((252829782495/4722366482869645213696), (231367712715/4722366482869645213696)), (165/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-366057403825/18889465931478580854784), (-13522821703/18889465931478580854784)), (251/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct7 : Sound J_gammaProduct7 F_gammaProduct7 c := by
  apply sound_round (sound_mul (A_gammaProduct6 hcre) (A_gammaInverse7 hcre) S_gammaProduct6 S_gammaInverse7)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct7, J_gammaProduct6, J_gammaInverse7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(8, 0), 0, by norm_num⟩
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

theorem S_q9 : Sound J_q9 F_q9 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (8, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((75/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_gammaFactor8 : Sound J_gammaFactor8 F_gammaFactor8 c := by
  apply sound_round (sound_add (A_base hcre) (A_q9 hcre) S_base S_q9)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor8, J_base, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5120000/48801867), (-661760/48801867)), 0, by norm_num⟩
  | 1 => ⟨((-1432026316800/264624691409521), (3388211200000/2381622222685689)), 0, by norm_num⟩
  | 2 => ⟨((154376299425/562949953421312), (-125333461377/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-245543496885/18014398509481984), (138687717347/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((191042645187/288230376151711744), (-143039114027/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((-72413686899/2305843009213693952), (140778982033/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((212567033043/147573952589676412928), (-8366783907/4611686018427387904)), (9/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-74682840785/1180591620717411303424), (247774493563/2361183241434822606848)), (5/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((49242791533/18889465931478580854784), (-112081748059/18889465931478580854784)), (11/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-116685289965/1208925819614629174706176), (99413485109/302231454903657293676544)), (11/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((54797446663/19342813113834066795298816), (-346413932487/19342813113834066795298816)), (11/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-8412799937/309485009821345068724781056), (148346955057/154742504910672534362390528)), (11/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-25124715213/4951760157141521099596496896), (-1952589327/38685626227668133590597632)), (21/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (1551/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (1551/1280)))⁻¹=value ((5120000/48801867), (-661760/48801867)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/48801867), (-661760/48801867))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-74862012345/144115188075855872), (-158932096221/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 1 => ⟨((348534265583/576460752303423488), (3810862751/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 2 => ⟨((-193826082713/576460752303423488), (34421532891/288230376151711744)), (17/1152921504606846976), by norm_num⟩
  | 3 => ⟨((7928472989/72057594037927936), (-260763648133/2305843009213693952)), (5/576460752303423488), by norm_num⟩
  | 4 => ⟨((-37769200555/2305843009213693952), (129687893359/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-83563063739/18446744073709551616), (-347177030641/18446744073709551616)), (31/18446744073709551616), by norm_num⟩
  | 6 => ⟨((38577407465/9223372036854775808), (76842513767/18446744073709551616)), (25/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-246218914477/147573952589676412928), (-50122919335/147573952589676412928)), (19/73786976294838206464), by norm_num⟩
  | 8 => ⟨((255873531005/590295810358705651712), (-111778581875/590295810358705651712)), (7/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-150124664181/2361183241434822606848), (263237912057/2361183241434822606848)), (41/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-23773354469/4722366482869645213696), (-321148316955/9444732965739290427392)), (123/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((31998549337/4722366482869645213696), (232858922453/37778931862957161709568)), (93/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-368732138123/151115727451828646838272), (-13557415791/151115727451828646838272)), (141/75557863725914323419136), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct8 : Sound J_gammaProduct8 F_gammaProduct8 c := by
  apply sound_round (sound_mul (A_gammaProduct7 hcre) (A_gammaInverse8 hcre) S_gammaProduct7 S_gammaInverse8)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct8, J_gammaProduct7, J_gammaInverse8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(9, 0), 0, by norm_num⟩
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

theorem S_q10 : Sound J_q10 F_q10 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (9, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((83/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_gammaFactor9 : Sound J_gammaFactor9 F_gammaFactor9 c := by
  apply sound_round (sound_add (A_base hcre) (A_q10 hcre) S_base S_q10)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor9, J_base, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16998400/178764001), (-1985280/178764001)), 0, by norm_num⟩
  | 1 => ⟨((-142502132940800/31956568053528001), (33746583552000/31956568053528001)), 0, by norm_num⟩
  | 2 => ⟨((232101530321/1125899906842624), (-84407210941/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-84531173707/9007199254740992), (169660473023/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((242140710139/576460752303423488), (-159102672077/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((-85031466585/4611686018427387904), (142543597245/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((233407960965/295147905179352825856), (-247086492397/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-77801481117/2361183241434822606848), (208697731669/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((49913359469/37778931862957161709568), (-172582531127/75557863725914323419136)), (11/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-121211863169/2417851639229258349412352), (280307969673/2417851639229258349412352)), (5/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((33651471671/19342813113834066795298816), (-1750012045/302231454903657293676544)), (9/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-15648264021/309485009821345068724781056), (352758539551/1237940039285380274899124224)), (17/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((16274298141/19807040628566084398385987584), (-34238411911/2475880078570760549798248448)), (1/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (1551/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (1551/1280)))⁻¹=value ((16998400/178764001), (-1985280/178764001)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/178764001), (-1985280/178764001))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-120956398477/2305843009213693952), (-11787066239/576460752303423488)), (11/4611686018427387904), by norm_num⟩
  | 1 => ⟨((139933282559/2305843009213693952), (-4633839367/4611686018427387904)), (13/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-309218032751/9223372036854775808), (142728499277/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 3 => ⟨((98825299495/9223372036854775808), (-237911770707/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-6321329781/4611686018427387904), (114419058073/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-11234666579/18446744073709551616), (-301319173809/147573952589676412928)), (31/147573952589676412928), by norm_num⟩
  | 6 => ⟨((71465649199/147573952589676412928), (261707346477/590295810358705651712)), (25/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-443685013823/2361183241434822606848), (-37964335035/1180591620717411303424)), (19/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227746669087/4722366482869645213696), (-105471315095/4722366482869645213696)), (7/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-65891629969/9444732965739290427392), (59675425871/4722366482869645213696)), (41/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-351103127/590295810358705651712), (-288398443143/75557863725914323419136)), (61/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((28796644185/37778931862957161709568), (104121484161/151115727451828646838272)), (23/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-330138976747/1208925819614629174706176), (-6019743361/604462909807314587353088)), (279/1208925819614629174706176), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct9 : Sound J_gammaProduct9 F_gammaProduct9 c := by
  apply sound_round (sound_mul (A_gammaProduct8 hcre) (A_gammaInverse9 hcre) S_gammaProduct8 S_gammaInverse9)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct9, J_gammaProduct8, J_gammaInverse9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(10, 0), 0, by norm_num⟩
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

theorem S_q11 : Sound J_q11 F_q11 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (10, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((91/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_gammaFactor10 : Sound J_gammaFactor10 F_gammaFactor10 c := by
  apply sound_round (sound_add (A_base hcre) (A_q11 hcre) S_base S_q11)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor10, J_base, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((18636800/214399201), (-1985280/214399201)), 0, by norm_num⟩
  | 1 => ⟨((-171694488780800/45967017389438401), (36999266304000/45967017389438401)), 0, by norm_num⟩
  | 2 => ⟨((178583912681/1125899906842624), (-29429317065/562949953421312)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-119828125467/18014398509481984), (27079870745/9007199254740992)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((317268429689/1152921504606846976), (-46539600719/288230376151711744)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((-103420006987/9223372036854775808), (76479083349/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((265013762491/590295810358705651712), (-243380467005/590295810358705651712)), (7/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-83131468671/4722366482869645213696), (188879793815/9444732965739290427392)), (3/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((203256715203/302231454903657293676544), (-143664469183/151115727451828646838272)), (5/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-60030566161/2417851639229258349412352), (214866974251/4835703278458516698824704)), (9/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((135148578597/154742504910672534362390528), (-158313567241/77371252455336267181195264)), (15/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-35264002911/1237940039285380274899124224), (57548949075/618970019642690137449562112)), (3/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((63986300279/79228162514264337593543950336), (-41326001545/9903520314283042199192993792)), (19/79228162514264337593543950336), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (1551/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (1551/1280)))⁻¹=value ((18636800/214399201), (-1985280/214399201)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/214399201), (-1985280/214399201))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-350425591683/73786976294838206464), (-23826971839/18446744073709551616)), (9/36893488147419103232), by norm_num⟩
  | 1 => ⟨((101056691869/18446744073709551616), (-45388715569/73786976294838206464)), (11/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-221817621593/73786976294838206464), (63002326293/36893488147419103232)), (15/73786976294838206464), by norm_num⟩
  | 3 => ⟨((34484552205/36893488147419103232), (-193093725909/147573952589676412928)), (17/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-56835275085/590295810358705651712), (361887092627/590295810358705651712)), (35/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-41616409685/590295810358705651712), (-29358084783/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 6 => ⟨((29624610373/590295810358705651712), (200106774641/4722366482869645213696)), (11/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-89768444681/4722366482869645213696), (-25166878221/9444732965739290427392)), (17/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((182242027289/37778931862957161709568), (-22291491117/9444732965739290427392)), (25/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-51996009873/75557863725914323419136), (24329171835/18889465931478580854784)), (73/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-38141658569/604462909807314587353088), (-465975794577/1208925819614629174706176)), (27/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((186574768279/2417851639229258349412352), (167546672189/2417851639229258349412352)), (163/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-266011504725/9671406556917033397649408), (-4794642205/4835703278458516698824704)), (123/4835703278458516698824704), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct10 : Sound J_gammaProduct10 F_gammaProduct10 c := by
  apply sound_round (sound_mul (A_gammaProduct9 hcre) (A_gammaInverse10 hcre) S_gammaProduct9 S_gammaInverse10)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct10, J_gammaProduct9, J_gammaInverse10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(11, 0), 0, by norm_num⟩
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

theorem S_q12 : Sound J_q12 F_q12 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (11, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((99/8), (1551/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
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
theorem S_gammaFactor11 : Sound J_gammaFactor11 F_gammaFactor11 c := by
  apply sound_round (sound_add (A_base hcre) (A_q12 hcre) S_base S_q12)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor11, J_base, J_q12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((204800/2558699), (-60160/7676097)), 0, by norm_num⟩
  | 1 => ⟨((-186934067200/58922465153409), (12320768000/19640821717803)), 0, by norm_num⟩
  | 2 => ⟨((280367233155/2251799813685248), (-21131471951/562949953421312)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-87113308047/18014398509481984), (71702687669/36028797018963968)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((26766519297/144115188075855872), (-28418403013/288230376151711744)), (3/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-32496773073/4611686018427387904), (172427748429/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 6 => ⟨((155657111329/590295810358705651712), (-126709868913/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-183453363837/18889465931478580854784), (181790043097/18889465931478580854784)), (7/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((26517970721/75557863725914323419136), (-255814082281/604462909807314587353088)), (11/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-119801877957/9671406556917033397649408), (44276340203/2417851639229258349412352)), (9/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((131215882885/309485009821345068724781056), (-120916465397/154742504910672534362390528)), (7/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-8607286923/618970019642690137449562112), (326157629731/9903520314283042199192993792)), (21/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((16933457293/39614081257132168796771975168), (-217481647569/158456325028528675187087900672)), (15/158456325028528675187087900672), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (1551/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (1551/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (1551/1280)))⁻¹=value ((204800/2558699), (-60160/7676097)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((204800/2558699), (-60160/7676097))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-57590519253/147573952589676412928), (-78113785995/1180591620717411303424)), (13/590295810358705651712), by norm_num⟩
  | 1 => ⟨((265363085937/590295810358705651712), (-1679612891/18446744073709551616)), (17/590295810358705651712), by norm_num⟩
  | 2 => ⟨((-144544456157/590295810358705651712), (195564970453/1180591620717411303424)), (23/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((174043463791/2361183241434822606848), (-141250760137/1180591620717411303424)), (27/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-3177473149/590295810358705651712), (259264637707/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-136038163849/18889465931478580854784), (-332244374447/18889465931478580854784)), (45/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((177794019171/37778931862957161709568), (138800987871/37778931862957161709568)), (9/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-131858540421/75557863725914323419136), (-29149179453/151115727451828646838272)), (55/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((264880343815/604462909807314587353088), (-136510509227/604462909807314587353088)), (81/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-149033665389/2417851639229258349412352), (288302375763/2417851639229258349412352)), (117/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-58723667071/9671406556917033397649408), (-85520293731/2417851639229258349412352)), (173/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((274709553037/38685626227668133590597632), (245013203123/38685626227668133590597632)), (65/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-194843345845/77371252455336267181195264), (-13839538251/154742504910672534362390528)), (49/19342813113834066795298816), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((253339250525/549755813888), (15882111925/274877906944)), (561/549755813888), by norm_num⟩
  | 1 => ⟨((71214793441/1099511627776), (247488646835/1099511627776)), (1417/549755813888), by norm_num⟩
  | 2 => ⟨((-158615000621/8796093022208), (171724755883/17592186044416)), (30501/8796093022208), by norm_num⟩
  | 3 => ⟨((43411961861/4398046511104), (62815157313/8796093022208)), (28069/8796093022208), by norm_num⟩
  | 4 => ⟨((-178229298079/70368744177664), (189124806847/70368744177664)), (38851/17592186044416), by norm_num⟩
  | 5 => ⟨((25974714717/140737488355328), (-180787673947/281474976710656)), (696467/562949953421312), by norm_num⟩
  | 6 => ⟨((47370056967/562949953421312), (63717883023/281474976710656)), (83683/140737488355328), by norm_num⟩
  | 7 => ⟨((-257094170781/4503599627370496), (-29079953425/1125899906842624)), (142963/562949953421312), by norm_num⟩
  | 8 => ⟨((296564674437/18014398509481984), (-8862433889/2251799813685248)), (55417/562949953421312), by norm_num⟩
  | 9 => ⟨((-97397571661/36028797018963968), (274933725323/72057594037927936)), (1269319/36028797018963968), by norm_num⟩
  | 10 => ⟨((-35291565/281474976710656), (-362341892931/288230376151711744)), (3404889/288230376151711744), by norm_num⟩
  | 11 => ⟨((144263795417/576460752303423488), (135848863057/576460752303423488)), (541655/144115188075855872), by norm_num⟩
  | 12 => ⟨((-430831844469/4611686018427387904), (-7500398607/2305843009213693952)), (2645747/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((253339250525/549755813888), (15882111925/274877906944)), (281/274877906944), by norm_num⟩
  | 1 => ⟨((71214793441/1099511627776), (247488646835/1099511627776)), (2835/1099511627776), by norm_num⟩
  | 2 => ⟨((-158615000621/8796093022208), (171724755883/17592186044416)), (61003/17592186044416), by norm_num⟩
  | 3 => ⟨((43411961861/4398046511104), (62815157313/8796093022208)), (56139/17592186044416), by norm_num⟩
  | 4 => ⟨((-178229298079/70368744177664), (189124806847/70368744177664)), (155407/70368744177664), by norm_num⟩
  | 5 => ⟨((25974714717/140737488355328), (-180787673947/281474976710656)), (348245/281474976710656), by norm_num⟩
  | 6 => ⟨((47370056967/562949953421312), (63717883023/281474976710656)), (334755/562949953421312), by norm_num⟩
  | 7 => ⟨((-257094170781/4503599627370496), (-29079953425/1125899906842624)), (1143885/4503599627370496), by norm_num⟩
  | 8 => ⟨((296564674437/18014398509481984), (-8862433889/2251799813685248)), (1774065/18014398509481984), by norm_num⟩
  | 9 => ⟨((-97397571661/36028797018963968), (274933725323/72057594037927936)), (2541521/72057594037927936), by norm_num⟩
  | 10 => ⟨((-35291565/281474976710656), (-362341892931/288230376151711744)), (3416419/288230376151711744), by norm_num⟩
  | 11 => ⟨((144263795417/576460752303423488), (135848863057/576460752303423488)), (2189679/576460752303423488), by norm_num⟩
  | 12 => ⟨((-430831844469/4611686018427387904), (-7500398607/2305843009213693952)), (2737981/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile005Gamma
