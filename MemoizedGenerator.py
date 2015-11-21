from itertools import count

def memoizedGenerator( gen ):
    _iter = gen()
    _cache = []

    def _gen():
        for n in count():
            if n < len(_cache):
                yield _cache[n]
            else:
                term = next(_iter)
                _cache.append(term)
                yield term

    return _gen
