import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Have

open Polynomial

/--
让 $\mathbb{Q}$ 是有理数的集合。一个函数 $f : \mathbb{Q} \to \mathbb{Q}$ 被称为\emph{aquaesulian}，
如果其满足以下性质：对于每个 $x, y \in \mathbb{Q}$，

$$ f(x + f(y)) = f(x) + y \qquad\text{或}\qquad f(f(x) + y) = x + f(y)。 $$

证明存在一个整数 $c$，使得对于任何 aquaesulian 函数 $f$，存在至多 $c$ 个不同的形如
$f(r) + f(-r)$ 的有理数 r， 并求 $c$ 的最小可能值。

解答：c=2
-/
theorem imo_2024_p6
    (IsAquaesulian : (ℚ → ℚ) → Prop)
    (IsAquaesulian_def : ∀ f, IsAquaesulian f ↔
      ∀ x y, f (x + f y) = f x + y ∨ f (f x + y) = x + f y) :
    IsLeast {(c : ℤ) | ∀ f, IsAquaesulian f → {(f r + f (-r)) | (r : ℚ)}.Finite ∧
      {(f r + f (-r)) | (r : ℚ)}.ncard ≤ c} 2 := by
  exists@?_
  · /- 设 f 是一个 aquaesulian 函数，且 f(0) = 0。
        我们声称 f(x) + f(-x) 至多有两个不同的值。 -/
    useλu b=>if j:u 0=0then by_contra λc=>?_ else ?_
    · -- 如果 f(x) + f(-x) 对所有 x 都为 0，那么我们完成了。
      suffices:({J|∃k,u k+u (-k)= J}) ⊆{0}
      · simp_all[this.antisymm]
      -- 否则，取一个 a 和 k，使得 f(a) + f(-a) = k ≠ 0。
      rintro - ⟨a, rfl⟩
      contrapose! c
      simp_all
      -- 如果我们能证明 f(x) + f(-x) 对所有 x 为 0 或 k，那么我们完成了。
      suffices:{U|∃examples6, (u) ‹ℚ› +u ( -‹_›)= U} ⊆{0,(u (a : Rat)+ (u<|@@↑(( (-a ))))) } ..
      · use ( Set.toFinite ( _) ).subset ↑@@this , (Set.ncard_le_ncard$ (((this )) ) ).trans (Set.ncard_pair$ Ne.symm (↑ ( (c)) ) ).le
      -- 现在我们继续证明 f(x) + f(-x) 对所有 x 为 0 或 k。
      rintro-⟨hz, rfl⟩
      -- 我们有 f(x + f(a)) = f(x) + a 或 f(f(x) + a) = x + f(a)。
      induction b @hz a
      · -- 第一步 “f.”：首先，考虑 f(x + f(a)) = f(x) + a 的情况。
        /- 第一步 “i.”：我们有 f(-a + f(x + f(a))) = f(-a) + (x + f(a))
            或 f(f(-a) + (x + f(a))) = -a + f(x + f(a))。 -/
        have:=b (-a)$ hz+u a
        /- 第一步 “ii.”：我们有 f(x + f(x)) = f(x) + x 或 f(f(x) + x) = x + f(x)。
            这简化为仅仅 f(x + f(x)) = x + f(x)。 -/
        have:=b hz hz
        /- 第一步 “iii.”：将步“f.”代入步“i.”，得到
            f(f(x)) = x + f(a) + f(-a) 或 f(x + f(a) + f(-a)) = f(x)。 -/
        simp_all[add_comm]
        /- 第一步 “iiii.”：我们有 f(-x + f(x + f(x))) = f(-x) + x + f(x)
            或 f(f(-x) + x + f(x)) = -x + f(x + f(x))。 -/
        have:=b (-hz) (hz+u ↑(hz))
        /- 将步“ii.”代入步“iv.”，我们有
            f(f(x)) = x + f(-x) + f(x) 或 f(x + f(-x) + f(x)) = f(x)。 -/
        simp_all[ add_assoc, C]
        induction this
        · -- 第一步 “vi.”：首先，考虑 f(f(x)) = x + f(-x) + f(x) 的情况。
          /- 第一步 “vi.1” 在这种情况下，步 “iii.” 简化为
              f(-x) + f(x) = f(a) + f(-a)
              或 f(x + f(a) + f(-a)) = f(x)。 在前一种情况下我们完成了，
              所以我们只考虑后一种情况。 -/
          simp_all
          /- 第一步 “vi.2” 我们有
              f(x + f(x + f(a) + f(-a))) = f(x) + x + (f(a) + f(-a)) 或
              f(f(x) + x + f(a) + f(-a)) = x + f(x + f(a) + f(-a))。 -/
          have:=b hz (hz+(u a+u (-a)))
          /- 第一步 “vi.3” 我们有
              f(x + f(a) + f(-a) + f(x + f(a) + f(-a)))
              = x + f(a) + f(-a) + f(x + f(a) + f(-a))。 -/
          have:=b (hz+(u a+u (-a)))$ hz+(u a+u (-a))
          /- 第一步 “vi.4” 将步 “vi.1。” 代入步 “vi.2” 得到
              f(x +f(x))=f(x)+x+(f(a)+f(-a)) 或 f(f(x)+x+f(a)+f(-a))=x+f(x)。
              第一步 “vi.5” 将步 “vi.1。” 代入步 “vi.3” 得到
              f(x+f(a)+f(-a)+f(x))= x + f(a) + f(-a) + f(x)。
              将步 “vi.5。” 代入步 “vi.4。” 并简化得到
              f(x +f(x))=f(x)+x+(f(a)+f(-a)) 或 f(a)+f(-a)=0。
              前一种情况通过步 “ii。” 简化为 f(a)+f(-a)=0，
              所以在这两种情况下我们都有矛盾。 -/
          use .inr$ by_contra$ by hint
        -- 第一步 “vii.” 现在，考虑 f(x + f(-x) + f(x)) = f(x) 的情况。
        /- 第一步 “vii.1”：我们有 f(x + f(x + f(-x) + f(x))) = f(x) + x + f(-x) + f(x)
            或 f(f(x) + x + f(-x) + f(x)) = x + f(x + f(-x) + f(x))。 -/
        have:=b hz$ hz+(u hz+u (-hz))
        /- 第一步 “vii.2”：我们有 f(f(x + f(-x) + f(x)) + x + f(-x) + f(x)) =
            x+ f(-x)+ f(x) + f(x+ f(-x) + f(x))。
            第一步 “vii.3”：将步 “vii。” 代入步 “vii.2。” 得到
            f(f(x)+x+f(-x)+f(x))= x + f(-x) + f(x) + f(x)。
            将步 “vii。” 代入步 “1。” 得到
            f(x+f(x))=f(x)+x+ f(-x) + f(x) 或
            f(f(x)+x+f(-x)+f(x))=x+f(x)。
            在第一种情况下我们可以将其代入步“ii。”，
            简化为 f(-x)+f(x)=0 如所期望的。
            在第二种情况下，我们可以将其代入步 “vii.3”，
            得到 f(-x)+f(x)=0 再次如所期望的。 -/
        cases b (hz+(u hz+u (-hz)))$ hz+(u hz+u (-hz))with|_=>hint
      -- 第一步 “g.” 现在，考虑 f(f(x) + a) = x + f(a) 的情况。
      /- 第一步 “i.” 我们有 f(-x + f(f(x) + a)) = f(-x) + (f(x) + a)
          或 f(f(-x) + f(x) + a) = -x + f(f(x) + a)。 -/
      have:=b (-hz) (u hz+a)
      have:=b$ -a
      /- 第一步 “ii.” 我们有 f(-a + f(f(x) + a)) = f(-a) + (f(x) + a)
          或 f(f(-a) + (f(x) + a)) = -a + f(f(x) + a)。 -/
      specialize this (u hz+a)
      /- 第一步 “iii.” 将步 “g.” 代入步 “i.” 得到
          f(f(a)) = f(-x) + (f(x) + a) 或 f(f(-x) + f(x) + a) = f(a)。
  .      第一步 “iv.” 将步 “g.” 代入步 “ii.” 得到
          f(-a + x + f(a)) = f(-a) + f(x) + a 或
          f(f(-a) + f(x) + a) = -a + x + f(a)。 -/
      simp_all[ ←add_assoc]
      have:=b 0
      have:=b
      -- 第一步 “v.” 我们有 f(a + f(a)) = a + f(a)。
      specialize b a a
      simp_all[add_comm]
      /- 第一步 “vi.” 我们有 f(-a + f(a + f(a))) = f(-a) + a + f(a) 或
          f(f(-a) + a + f(a)) = -a + f(a + f(a))。 -/
      have:=(this<| -a) (↑a + (((u a))): (↑_ :((( _) ) ) )) ..
      /- 第一步 “vii.” 将步 “v.” 代入步 “vi。” 简化得到
          f(f(a)) = a + f(a) + f(-a) 或 f(a + f(a) + f(-a)) = f(a)。 -/
      simp_all[add_assoc]
      cases this
      · -- 第一步 “viii.” 首先，考虑 f(f(a)) = a + f(a) + f(-a) 的情况。
        /- 第一步 “viii.1” 在这种情况下，步 “iii。” 简化为
            f(a) + f(-a) = f(-x) + f(x)
            或 f(f(-x) + f(x) + a) = f(a)。
            在第一种情况下我们完成了，所以我们只考虑第二种情况。 -/
        simp_all
        contrapose! IsAquaesulian_def
        simp_all
        exfalso
        /- 第一步 “viii.2” 我们有
            f(a + f(a + (f(x) + f(-x)))) = a + (f(x) + f(-x)) + f(a) 或
            f(a+(f(x) + f(-x))+ f(a)) = a + f(a + (f(x) + f(-x)))。 -/
        have:=this a (a+(u hz+u (-hz)))
        simp_all[Ne.symm,Bool]
        /- 第一步 “viii.3” 我们有
            f(a + f(x) + f(-x) + f(a + f(x) + f(-x)))
            = a + f(x) + f(-x) + f(a + f(x) + f(-x))。 -/
        have:=‹∀congr_arg G,_› (a+(u hz+u (-hz)))$ a+(u ↑hz+u ↑( -hz) )
        /- 第一步 “viii.4” 将步 “viii.1” 代入步 “viii.3” 得到
            f(a + f(x) + f(-x) + f(a)) = a + f(x) + f(-x) + f(a)。
            结果通过对步 “viii.2” 进行情形分析跟随；在第一种情况下，
            将其代入步 “viii.1” 然后步 “v。”，得到 f(x) + f(-x) = 0 如所期望的，
            在第二种情况下，将其代入步 “viii.4” 然后步 “viii.1”，
            再次得到 f(x) + f(-x) = 0 如所期望的。
        -/
        simp_all
      -- 第一步 “ix.” 现在，考虑 f(a + f(a) + f(-a)) = f(a) 的情况。
      /- 第一步 “ix.1.” 我们有 f(a + f(a + f(a) + f(-a))) = f(a)+ a + f(a)+ f(-a)
          或 f(f(a)+ a + f(a)+ f(-a)) = a + f(a + f(a)+ f(-a))。 -/
      have:=this a (a +(u a+u (-a)))
      /- 第一步 “ix.2.” 我们有
          f(a + f(a) + f(-a) + f(a + f(a) + f(-a)))
          = a + f(a) + f(-a) + f(a + f(a) + f(-a))。
          第一步 “ix.3.” 将步 “ix。” 代入步 “ix.2” 得到
          f(a + f(a) + f(-a) + f(a)) = a + f(a) + f(-a) + f(a)。
          结果通过对步 “ix.1。” 进行情形分析：在第一种情况下，
          我们可以将其代入步“ix。”，然后步“v。”得到 f(a) + f(-a) = 0，
          在第二种情况下我们可以将其代入步“ix.3”然后步“ix。”，
          再次得到 f(a) + f(-a) = 0。
          无论哪种情况，这都与我们关于 a 的假设相矛盾。 -/
      cases‹forall Jd S,_› (a+(u a+u (-a))) ( a + (u a +u ↑(-a)))with| _ =>hint
    /- 现在设 f 是一个 f(0) ≠ 0 的 aquaesulian 函数。
        我们将推导出一个矛盾。 -/
    simp_all
    /- 我们有：
        P(0, 0) -> f(f(0)) = f(0),
        P(f(0), f(0)) -> f(f(0) + f(f(0))) = f(0) + f(f(0)) ->
        f(2f(0)) = 2f(0),
        P(0, f(0)) -> f(f(f(0))) = 2f(0) 或 f(2f(0)) = f(f(0)) ->
        f(0) = 2f(0) 或 f(2f(0)) = f(0) -> f(0) = 2f(0) 或 2f(0) = f(0)，
        因此，按照期望， f(0) = 0。 -/
    cases b 0 0with|_=>exact absurd (b 0$ (0+(1 *(@(u ↑.((0) )))))^ 01: ↑ ((_)) ) (id$ (by(cases ( b (u 0) ( (u 0)))with|_ => continuity)))
  rintro K V
  -- 现在让 f(x) = -x + 2⌈x⌉。我们声称 f 是 aquaesulian。
  specialize V $ λ N=>-N+2 *Int.ceil N
  specialize( V $ (IsAquaesulian_def _).mpr _)
  · simp_rw [ ←eq_sub_iff_add_eq']
    /- 泛函方程简化为
        ⌈x - y + ⌈y⌉ * 2⌉ * 2 = ⌈y⌉ * 2 + ⌈x⌉ * 2 或
        ⌈-x + y + ⌈x⌉ * 2⌉ * 2 = ⌈y⌉ * 2 + ⌈x⌉ * 2。 -/
    ring
    use mod_cast@?_
    /- 这相当于：
        (A) ⌈y⌉ + ⌈x⌉ - 1 < x - y + ⌈y⌉ * 2 ≤ ⌈y⌉ + ⌈x⌉ 或
        (B) ⌈y⌉ + ⌈x⌉ - 1 < -x + y + ⌈x⌉ * 2 ≤ ⌈y⌉ + ⌈x⌉ -/
    norm_num[<-add_mul,Int.ceil_eq_iff]
    useλc K=>(em _).imp (⟨by linarith[Int.ceil_lt_add_one c,Int.le_ceil K],.⟩) (by repeat use by linarith[.,Int.le_ceil c,or,Int.ceil_lt_add_one$ K])
    /- 如果 x - y + ⌈y⌉ * 2 ≤ ⌈y⌉ + ⌈x⌉ 成立，那么我们得到所需的结果 (A)，
        因为 ⌈y⌉ < y + 1。
        否则，我们有 ⌈y⌉ + ⌈x⌉ < x - y + ⌈y⌉ * 2，我们取反并
        添加 ⌈x⌉ * 2 + ⌈y⌉ * 2 得到 -x + y + ⌈x⌉ * 2 < ⌈y⌉ + ⌈x⌉，
        从而得到所需的结果 (B)，因为 ⌈x⌉ < x + 1。 -/
  simp_all[Int.ceil_neg, ←add_assoc]
  suffices:2<=V.1.toFinset.card
  · let M:=V.1.toFinset
    norm_num[this,V.2.trans',(Set.ext$ by simp_all[M]: {x :Rat|∃t:Rat, (↑2 ) * ( ⌈ t ⌉:(ℚ ) ) .. + (- (2 *⌊(t)⌋)) = ↑x} = M)]
  /- 最后，我们有 f(-1) + f(1) = 0 和 f(1/2) = f(-1/2) = 2
      作为 f 的两个不同的值。因此，c = 2 是确切的。 -/
  use Finset.one_lt_card.2$ by exists@0,V.1.mem_toFinset.2 (by exists-1),2,V.1.mem_toFinset.2 (by exists 1/2)

#print axioms imo_2024_p6
