"""Small counterexamples on AMD models: two schedules (block orders) of the same blocks give
different results under (a) anchoring, (b) pinning; and the CDNA3 pinned positive check."""
import random
import fastmodels as FM
S0 = FM.S0
rng = random.Random(3)
w16 = FM.f16_word

def chain_words(P, blocks, c):
    for b in blocks:
        c = FM.block_terms(P, FM.prods(P, b), c)
    return c

def search(P, mode, nblocks=2, tries=20000):
    K = P.K
    for t in range(tries):
        if mode == 'pinned':
            G = K - 2
            pin = [(0x5000, 0x5000), (0xD000, 0x5000)]   # +-2^10
        else:
            G = K
        blocks = []
        for _ in range(nblocks):
            blocks.append([(w16(rng.uniform(-2, 2)), w16(rng.uniform(-2, 2))) for _ in range(G)] + (pin if mode == 'pinned' else []))
        if mode == 'anchored':
            c0 = 3 << (9 + S0)     # 1.5 * 2^10
        else:
            c0 = 0
        r1 = chain_words(P, blocks, c0)
        r2 = chain_words(P, blocks[::-1], c0)
        if r1 != r2:
            return blocks, c0, r1, r2
    return None

for P in (FM.CDNA1, FM.CDNA2, FM.CDNA3):
    for mode in ('anchored', 'pinned'):
        res = search(P, mode)
        if res is None:
            print(P.name, mode, 'no counterexample found (2 blocks, 20000 tries)')
        else:
            blocks, c0, r1, r2 = res
            print(P.name, mode, 'c0', hex(FM.units_to_f32word(c0)), 'order1', hex(FM.units_to_f32word(r1)), 'order2', hex(FM.units_to_f32word(r2)))
            print('   blocks', [[(hex(a), hex(b)) for a, b in blk] for blk in blocks])
