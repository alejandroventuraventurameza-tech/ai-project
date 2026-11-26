"""Integer check of selector-word multiplicities; no economic states or paths."""
from itertools import product
from pathlib import Path
import json

expected={(0,0):9,(0,1):3,(1,0):3,(1,1):1}
checked=0
for first in range(4):
    for next_choices in product(range(4),repeat=4):
        counts={word:0 for word in expected}
        for a,b in product(range(4),repeat=2):
            counts[(int(a==first),int(b==next_choices[a]))]+=1
        assert counts==expected
        checked+=1
result={'depth':2,'all_node_selector_configurations_checked':checked,
        'word_multiplicities':{str(k):v for k,v in expected.items()},
        'scope':__doc__,
        'limits':'The all-depth assertion is proved by induction in the text; this exact finite check complements it.'}
Path(__file__).with_name('selector_tree_check.json').write_text(json.dumps(result, indent=2), encoding='utf-8', newline='\n')
print(json.dumps(result,indent=2))
