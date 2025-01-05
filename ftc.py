# %%
import sage.all
from typing import List
from collections.abc import Callable
from sage.matrix.berlekamp_massey import berlekamp_massey
import itertools

#%%
P = 3
F = [
    #  lambda x:P*x,
     lambda x:P*x+1, 
     lambda x:P*x+2,
     lambda x:2*P*x+1
     ]

# %%
'''
P : int, which p-adic system to be working over
F : List[Callable[[int],int], the IFS construction
max_layers : int, number of iteration layers

returns a tuple of:
array representing number of representatives at the layer, and
sage polynomial representing the linear recurrence
of the number of representatives at every layer
~~~
note that the runtime in worst case scales with P^layers,
use this to choose layers
'''
def get_recurrence(
    P: int, 
    F: List[Callable[[int],int]], 
    max_layers=12,
    verbose=False):
    # berlekamp massey requires list len to be even
    assert(max_layers%2 == 0)
    # use a set to avoid duplicates
    residues = {0}
    layer = 0
    modulo = 1
    past_residues = []
    residue_sizes = []

    while layer < max_layers: 
        if verbose: print(layer)#, residues)
        layer += 1
        modulo *= P
        new_residues = {f(e)%modulo
            for e in residues for f in F}
        # if layer < 5: print(new_residues)
        residues = new_residues.copy()
        past_residues.append(new_residues.copy())
        residue_sizes += [len(residues)]
    
    # print(residue_sizes)
    # return berlekamp_massey(residue_sizes)
    return residue_sizes, past_residues

# %%
# fix P = something
P = 3
seen_recurrences = set()
interesting_polys = dict()
for us in itertools.product(range(5), repeat=2):
    u2,u3 = us
    print(u2, u3)
    for ds in itertools.product(range(5), repeat=2):
        d2,d3=ds
        F = [lambda x: P*x,
             lambda x: u2*P*x + d2,
             lambda x: u3*P*x + d3]
        layers = 10
        representatives, _ = get_recurrence(P, F, layers)
        representatives = tuple(representatives)
        if representatives in seen_recurrences:
            continue
        seen_recurrences.add(representatives)
        min_poly = berlekamp_massey(representatives)
        if min_poly.degree() < layers/2:
            # berlekamp massey returns linear recurrence of
            # length layers/2 if nothing interesting was found
            if interesting_polys.get(min_poly):
                interesting_polys[min_poly].append((u2,u3,d2,d3))
            else:
                interesting_polys[min_poly] = [(u2,u3,d2,d3)]

# %%
F = [lambda x: P*x,
        lambda x: 2*P*x + 3,
        lambda x: P*x + 1]

# %%
rec, past_residues= get_recurrence(P, F, max_layers=16, verbose=True)
berlekamp_massey(rec)

# %%
