# Lean verification of Partitioning 3-homogeneous latin bitrades

My 2008 paper on partitioning 3-homogeneous latin bitrades: <https://link.springer.com/article/10.1007/s10711-008-9242-4>

Open access: <https://arxiv.org/abs/0710.0938>

Current events involving OpenAI and Lean:

<https://social.coop/@cwebber/117236126658335889>

<https://www.abc.net.au/news/2026-09-10/openai-navier-stokes-millennium-problem-claims/107132242>

Naturally I wondered, could we formalise my paper automatically? I've had "learn Lean" on my todo list for a long time...

Codex's overview: [CODEX-README.md](CODEX-README.md)

Codex's initial review, formalisation, and final review: [CODEX-REVIEW-2026-09-11.md](CODEX-REVIEW-2026-09-11.md)

Claude reviewing Codex: [CLAUDE-REVIEW-2026-09-11.md](CLAUDE-REVIEW-2026-09-11.md)

The main theorem:

```lean
theorem theorem_1_1
    (positive negative : Finset (Entry Row Column Symbol))
    (hbit : IsBitrade positive negative)
    (hhom : IsKHomogeneous 3 positive) :
    ∃ T₀ T₁ T₂,
      IsThreeTransversalPartition positive T₀ T₁ T₂
```

[lean blueprint PDF](print.pdf)

I'm impressed.

