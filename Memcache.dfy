module Types {
    type Key = int
    type Value = int
    type Time = int

    datatype StoreEntry = StoreEntry(key: Key, val: Value, exp: Time)
    datatype Option<T> = None | Some(value: T)

    predicate isLive(e: StoreEntry, now: Time)
    {
        e.exp > now
    }

    predicate UniqueKeys(store: seq<StoreEntry>)
    {
        forall i, j :: 0 <= i < j < |store| ==> store[i].key != store[j].key
    }

    function FindIndex(store: seq<StoreEntry>, k: Key): int
        ensures -1 <= FindIndex(store, k) < |store|
        ensures FindIndex(store, k) >= 0 ==> store[FindIndex(store, k)].key == k
        ensures FindIndex(store, k) == -1 ==> forall i :: 0 <= i < |store| ==> store[i].key != k
    {
        FindIndexHelper(store, k, 0)
    }

    function FindIndexHelper(store: seq<StoreEntry>, k: Key, start: nat): int
        requires start <= |store|
        ensures -1 <= FindIndexHelper(store, k, start) < |store|
        ensures FindIndexHelper(store, k, start) >= 0 ==> store[FindIndexHelper(store, k, start)].key == k
        ensures FindIndexHelper(store, k, start) == -1 ==> forall i :: start <= i < |store| ==> store[i].key != k
        decreases |store| - start
    {
        if start >= |store| then -1
        else if store[start].key == k then start
        else FindIndexHelper(store, k, start + 1)
    }

    predicate keyLive(store: seq<StoreEntry>, k: Key, now: Time)
    {
        var idx := FindIndex(store, k);
        idx >= 0 && isLive(store[idx], now)
    }

    predicate keyDead(store: seq<StoreEntry>, k: Key, now: Time)
    {
        var idx := FindIndex(store, k);
        idx == -1 || !isLive(store[idx], now)
    }
}

module Abstraction {
    import opened Types

    ghost function Map(store: seq<StoreEntry>, now: Time): map<Key, Value>
        decreases |store|
    {
        if |store| == 0 then
            map[]
        else
            var e := store[0];
            var rest := Map(store[1..], now);
            if isLive(e, now) then
                rest[e.key := e.val]
            else
                rest
    }

    lemma isInMap(store: seq<StoreEntry>, k: Key, now: Time)
        requires UniqueKeys(store)
        requires FindIndex(store, k) >= 0
        requires isLive(store[FindIndex(store, k)], now)
        ensures k in Map(store, now)
        ensures Map(store, now)[k] == store[FindIndex(store, k)].val
        decreases |store|
    {
        if |store| == 0 {
            assert false;
        } else {
            var e := store[0];
            var rest := Map(store[1..], now);
            var idx := FindIndex(store, k);
            if e.key == k {
                assert idx == 0;
                assert isLive(e, now);
            } else {
                assert idx > 0;
                UniqueKeysTail(store);
                FindIndexTail(store, k);
                isInMap(store[1..], k, now);
            }
        }
    }

    lemma notInMap(store: seq<StoreEntry>, k: Key, now: Time)
        requires UniqueKeys(store)
        requires FindIndex(store, k) == -1 || !isLive(store[FindIndex(store, k)], now)
        ensures k !in Map(store, now)
        decreases |store|
    {
        if |store| == 0 {
        } else {
            var e := store[0];
            var rest := Map(store[1..], now);
            UniqueKeysTail(store);
            var idx := FindIndex(store, k);
            if e.key == k {
                assert idx == 0;
                assert !isLive(e, now);
                notInMapTail(store[1..], k, now);
            } else {
                FindIndexTail(store, k);
                notInMap(store[1..], k, now);
            }
        }
    }

    lemma notInMapTail(store: seq<StoreEntry>, k: Key, now: Time)
        requires UniqueKeys(store)
        requires FindIndex(store, k) == -1
        ensures k !in Map(store, now)
        decreases |store|
    {
        if |store| == 0 {
        } else {
            UniqueKeysTail(store);
            FindIndexTail(store, k);
            notInMapTail(store[1..], k, now);
        }
    }

    lemma inMapIff(store: seq<StoreEntry>, k: Key, now: Time)
        requires UniqueKeys(store)
        ensures k in Map(store, now) <==> (FindIndex(store, k) >= 0 && isLive(store[FindIndex(store, k)], now))
    {
        var idx := FindIndex(store, k);
        if idx >= 0 && isLive(store[idx], now) {
            isInMap(store, k, now);
        } else {
            notInMap(store, k, now);
        }
    }

    lemma UniqueKeysTail(store: seq<StoreEntry>)
        requires |store| > 0
        requires UniqueKeys(store)
        ensures UniqueKeys(store[1..])
    {
        forall i, j | 0 <= i < j < |store[1..]|
            ensures store[1..][i].key != store[1..][j].key
        {
            assert store[1..][i] == store[i+1];
            assert store[1..][j] == store[j+1];
        }
    }

    lemma FindIndexTail(store: seq<StoreEntry>, k: Key)
        requires |store| > 0
        requires store[0].key != k
        ensures FindIndex(store, k) == if FindIndex(store[1..], k) == -1 then -1 else FindIndex(store[1..], k) + 1
        ensures FindIndex(store[1..], k) >= 0 ==> store[1..][FindIndex(store[1..], k)] == store[FindIndex(store, k)]
    {
        // FindIndex(store, k) starts at index 0, but store[0].key != k
        // So it recurses to FindIndexHelper(store, k, 1)
        // FindIndex(store[1..], k) = FindIndexHelper(store[1..], k, 0)
        // These are equivalent modulo index offset
        assert FindIndex(store, k) == FindIndexHelper(store, k, 0);
        assert store[0].key != k;
        assert FindIndex(store, k) == FindIndexHelper(store, k, 1);
        
        // Prove the relationship by induction on |store| - handled by Dafny
        FindIndexTailHelper(store, k, 0);
    }
    
    lemma FindIndexTailHelper(store: seq<StoreEntry>, k: Key, start: nat)
        requires |store| > 0
        requires start < |store|
        requires store[0].key != k
        ensures FindIndexHelper(store, k, start + 1) == 
                if FindIndexHelper(store[1..], k, start) == -1 then -1 
                else FindIndexHelper(store[1..], k, start) + 1
        decreases |store| - start
    {
        if start + 1 >= |store| {
            assert FindIndexHelper(store, k, start + 1) == -1;
            assert start >= |store[1..]|;
            assert FindIndexHelper(store[1..], k, start) == -1;
        } else if store[start + 1].key == k {
            assert store[1..][start].key == store[start + 1].key == k;
            assert FindIndexHelper(store, k, start + 1) == start + 1;
            assert FindIndexHelper(store[1..], k, start) == start;
        } else {
            assert store[1..][start].key == store[start + 1].key != k;
            FindIndexTailHelper(store, k, start + 1);
        }
    }
}

module Helpers {
    import opened Types
    import opened Abstraction

    function seqRemove<T>(s: seq<T>, idx: int): seq<T>
        requires 0 <= idx < |s|
        ensures |seqRemove(s, idx)| == |s| - 1
    {
        s[..idx] + s[idx+1..]
    }

    lemma UniqueKeysAfterUpdate(store: seq<StoreEntry>, idx: int, e: StoreEntry)
        requires UniqueKeys(store)
        requires 0 <= idx < |store|
        requires e.key == store[idx].key
        ensures UniqueKeys(store[idx := e])
    {
        var newStore := store[idx := e];
        forall i, j | 0 <= i < j < |newStore|
            ensures newStore[i].key != newStore[j].key
        {
            if i == idx {
                assert newStore[i].key == e.key == store[idx].key;
                assert newStore[j].key == store[j].key;
            } else if j == idx {
                assert newStore[i].key == store[i].key;
                assert newStore[j].key == e.key == store[idx].key;
            } else {
                assert newStore[i].key == store[i].key;
                assert newStore[j].key == store[j].key;
            }
        }
    }

    lemma UniqueKeysAfterAppend(store: seq<StoreEntry>, e: StoreEntry)
        requires UniqueKeys(store)
        requires FindIndex(store, e.key) == -1
        ensures UniqueKeys(store + [e])
    {
        var newStore := store + [e];
        forall i, j | 0 <= i < j < |newStore|
            ensures newStore[i].key != newStore[j].key
        {
            if j == |store| {
                assert newStore[j].key == e.key;
                assert newStore[i].key == store[i].key;
                assert store[i].key != e.key;
            } else {
                assert newStore[i].key == store[i].key;
                assert newStore[j].key == store[j].key;
            }
        }
    }

    lemma UniqueKeysAfterRemove(store: seq<StoreEntry>, idx: int)
        requires UniqueKeys(store)
        requires 0 <= idx < |store|
        ensures UniqueKeys(seqRemove(store, idx))
    {
        var newStore := seqRemove(store, idx);
        forall i, j | 0 <= i < j < |newStore|
            ensures newStore[i].key != newStore[j].key
        {
            var oi := if i < idx then i else i + 1;
            var oj := if j < idx then j else j + 1;
            assert newStore[i].key == store[oi].key;
            assert newStore[j].key == store[oj].key;
        }
    }

    lemma FindIndexAfterUpdate(store: seq<StoreEntry>, idx: int, e: StoreEntry, k: Key)
        requires UniqueKeys(store)
        requires 0 <= idx < |store|
        requires e.key == store[idx].key
        ensures FindIndex(store[idx := e], k) == FindIndex(store, k)
    {
        var newStore := store[idx := e];
        UniqueKeysAfterUpdate(store, idx, e);
        if FindIndex(store, k) >= 0 {
            var i := FindIndex(store, k);
            assert newStore[i].key == if i == idx then e.key else store[i].key;
            assert newStore[i].key == store[i].key == k;
        }
    }

    lemma FindIndexAfterAppend(store: seq<StoreEntry>, e: StoreEntry, k: Key)
        requires UniqueKeys(store)
        requires FindIndex(store, e.key) == -1
        ensures FindIndex(store + [e], k) == if k == e.key then |store| else FindIndex(store, k)
    {
        var newStore := store + [e];
        UniqueKeysAfterAppend(store, e);
        FindIndexAfterAppendHelper(store, e, k, 0);
    }
    
    lemma FindIndexAfterAppendHelper(store: seq<StoreEntry>, e: StoreEntry, k: Key, start: nat)
        requires start <= |store|
        requires UniqueKeys(store)
        requires FindIndex(store, e.key) == -1
        ensures FindIndexHelper(store + [e], k, start) == 
                if k == e.key then 
                    if FindIndexHelper(store, k, start) == -1 then |store| else FindIndexHelper(store, k, start)
                else FindIndexHelper(store, k, start)
        decreases |store| - start
    {
        var newStore := store + [e];
        if start >= |store| {
            // At the appended element
            if k == e.key {
                assert newStore[start] == e;
                assert newStore[start].key == k;
                assert FindIndexHelper(newStore, k, start) == start;
            } else {
                assert newStore[start].key != k;
                assert FindIndexHelper(newStore, k, start + 1) == -1;
            }
        } else if store[start].key == k {
            assert newStore[start].key == k;
        } else {
            FindIndexAfterAppendHelper(store, e, k, start + 1);
        }
    }

    lemma updateKeyOthersIntact(store: seq<StoreEntry>, idx: int, e: StoreEntry, other: Key, now: Time)
        requires UniqueKeys(store)
        requires 0 <= idx < |store|
        requires e.key == store[idx].key
        requires e.key != other
        ensures (other in Map(store[idx := e], now)) == (other in Map(store, now))
        ensures other in Map(store, now) ==> Map(store[idx := e], now)[other] == Map(store, now)[other]
    {
        var newStore := store[idx := e];
        UniqueKeysAfterUpdate(store, idx, e);
        FindIndexAfterUpdate(store, idx, e, other);
        inMapIff(store, other, now);
        inMapIff(newStore, other, now);
        if other in Map(store, now) {
            isInMap(store, other, now);
            isInMap(newStore, other, now);
            MapUpdatePreservesOther(store, idx, e, other, now);
        }
    }

    lemma MapUpdatePreservesOther(store: seq<StoreEntry>, idx: int, e: StoreEntry, other: Key, now: Time)
        requires UniqueKeys(store)
        requires 0 <= idx < |store|
        requires e.key == store[idx].key
        requires e.key != other
        requires FindIndex(store, other) >= 0
        requires isLive(store[FindIndex(store, other)], now)
        ensures other in Map(store, now)
        ensures other in Map(store[idx := e], now)
        ensures Map(store[idx := e], now)[other] == Map(store, now)[other]
        decreases |store|
    {
        var newStore := store[idx := e];
        UniqueKeysAfterUpdate(store, idx, e);
        isInMap(store, other, now);
        FindIndexAfterUpdate(store, idx, e, other);
        if |store| == 0 {
        } else {
            var se := store[0];
            var ne := newStore[0];
            if idx == 0 {
                UniqueKeysTail(store);
                UniqueKeysTail(newStore);
                assert newStore[1..] == store[1..];
            } else {
                UniqueKeysTail(store);
                UniqueKeysTail(newStore);
                assert newStore[1..] == store[1..][idx-1 := e];
                if se.key == other {
                } else {
                    FindIndexTail(store, other);
                    MapUpdatePreservesOther(store[1..], idx-1, e, other, now);
                }
            }
        }
    }

    lemma appendKeyOthersIntact(store: seq<StoreEntry>, e: StoreEntry, other: Key, now: Time)
        requires UniqueKeys(store)
        requires FindIndex(store, e.key) == -1
        requires e.key != other
        ensures (other in Map(store + [e], now)) == (other in Map(store, now))
        ensures other in Map(store, now) ==> Map(store + [e], now)[other] == Map(store, now)[other]
    {
        var newStore := store + [e];
        UniqueKeysAfterAppend(store, e);
        FindIndexAfterAppend(store, e, other);
        inMapIff(store, other, now);
        inMapIff(newStore, other, now);
        if other in Map(store, now) {
            isInMap(store, other, now);
            isInMap(newStore, other, now);
            MapAppendPreservesOther(store, e, other, now);
        }
    }

    lemma MapAppendPreservesOther(store: seq<StoreEntry>, e: StoreEntry, other: Key, now: Time)
        requires UniqueKeys(store)
        requires FindIndex(store, e.key) == -1
        requires e.key != other
        requires FindIndex(store, other) >= 0
        requires isLive(store[FindIndex(store, other)], now)
        ensures other in Map(store, now)
        ensures other in Map(store + [e], now)
        ensures Map(store + [e], now)[other] == Map(store, now)[other]
        decreases |store|
    {
        var newStore := store + [e];
        UniqueKeysAfterAppend(store, e);
        isInMap(store, other, now);
        FindIndexAfterAppend(store, e, other);
        if |store| == 0 {
        } else {
            var se := store[0];
            UniqueKeysTail(store);
            assert newStore[1..] == store[1..] + [e];
            if se.key == other {
                isInMap(newStore, other, now);
            } else {
                FindIndexTail(store, other);
                FindIndexTail(store, e.key);
                MapAppendPreservesOther(store[1..], e, other, now);
            }
        }
    }

    lemma removeKeyOthersIntact(store: seq<StoreEntry>, idx: int, other: Key, now: Time)
        requires UniqueKeys(store)
        requires 0 <= idx < |store|
        requires store[idx].key != other
        ensures (other in Map(seqRemove(store, idx), now)) == (other in Map(store, now))
        ensures other in Map(store, now) ==> Map(seqRemove(store, idx), now)[other] == Map(store, now)[other]
    {
        var newStore := seqRemove(store, idx);
        UniqueKeysAfterRemove(store, idx);
        FindIndexAfterRemove(store, idx, other);
        inMapIff(store, other, now);
        inMapIff(newStore, other, now);
        if other in Map(store, now) {
            isInMap(store, other, now);
            isInMap(newStore, other, now);
            MapRemovePreservesOther(store, idx, other, now);
        }
    }

    lemma FindIndexAfterRemove(store: seq<StoreEntry>, idx: int, k: Key)
        requires UniqueKeys(store)
        requires 0 <= idx < |store|
        requires store[idx].key != k
        ensures var newStore := seqRemove(store, idx);
                var oldIdx := FindIndex(store, k);
                FindIndex(newStore, k) == if oldIdx == -1 then -1 else if oldIdx < idx then oldIdx else oldIdx - 1
    {
        var newStore := seqRemove(store, idx);
        UniqueKeysAfterRemove(store, idx);
        var oldIdx := FindIndex(store, k);
        if oldIdx == -1 {
            // k not in store, so not in newStore either
            forall i | 0 <= i < |newStore|
                ensures newStore[i].key != k
            {
                var oi := if i < idx then i else i + 1;
                assert newStore[i] == store[oi];
            }
        } else if oldIdx < idx {
            // k is before the removed element
            assert newStore[oldIdx] == store[oldIdx];
            assert newStore[oldIdx].key == k;
        } else {
            // k is after the removed element (oldIdx > idx since store[idx].key != k)
            assert oldIdx > idx;
            assert newStore[oldIdx - 1] == store[oldIdx];
            assert newStore[oldIdx - 1].key == k;
        }
    }

    lemma MapRemovePreservesOther(store: seq<StoreEntry>, idx: int, other: Key, now: Time)
        requires UniqueKeys(store)
        requires 0 <= idx < |store|
        requires store[idx].key != other
        requires FindIndex(store, other) >= 0
        requires isLive(store[FindIndex(store, other)], now)
        ensures other in Map(store, now)
        ensures other in Map(seqRemove(store, idx), now)
        ensures Map(seqRemove(store, idx), now)[other] == Map(store, now)[other]
        decreases |store|
    {
        var newStore := seqRemove(store, idx);
        UniqueKeysAfterRemove(store, idx);
        isInMap(store, other, now);
        FindIndexAfterRemove(store, idx, other);
        if |store| == 0 {
        } else if idx == 0 {
            assert newStore == store[1..];
            UniqueKeysTail(store);
            if store[0].key == other {
                assert false;
            }
            isInMap(newStore, other, now);
        } else {
            var se := store[0];
            UniqueKeysTail(store);
            assert newStore == [se] + seqRemove(store[1..], idx - 1);
            if se.key == other {
                isInMap(newStore, other, now);
            } else {
                FindIndexTail(store, other);
                FindIndexAfterRemoveTail(store, idx, se.key);
                MapRemovePreservesOther(store[1..], idx - 1, other, now);
                MapPrependPreserves(se, seqRemove(store[1..], idx - 1), other, now);
            }
        }
    }
    
    lemma FindIndexAfterRemoveTail(store: seq<StoreEntry>, idx: int, k: Key)
        requires UniqueKeys(store)
        requires |store| > 0
        requires 0 < idx < |store|
        requires store[0].key == k
        ensures FindIndex(seqRemove(store[1..], idx - 1), k) == -1
    {
        var tail := store[1..];
        var newTail := seqRemove(tail, idx - 1);
        UniqueKeysTail(store);
        UniqueKeysAfterRemove(tail, idx - 1);
        // k is at store[0], but tail = store[1..] doesn't contain k (UniqueKeys)
        forall i | 0 <= i < |tail|
            ensures tail[i].key != k
        {
            assert tail[i] == store[i + 1];
            // store[0].key == k and UniqueKeys means store[i+1].key != k for i+1 > 0
        }
        // newTail is a subset of tail, so also doesn't contain k
        forall i | 0 <= i < |newTail|
            ensures newTail[i].key != k
        {
            var oi := if i < idx - 1 then i else i + 1;
            assert newTail[i] == tail[oi];
        }
    }

    lemma MapPrependPreserves(e: StoreEntry, store: seq<StoreEntry>, k: Key, now: Time)
        requires UniqueKeys(store)
        requires e.key != k
        requires FindIndex(store, e.key) == -1
        requires k in Map(store, now)
        ensures Map([e] + store, now)[k] == Map(store, now)[k]
    {
        var newStore := [e] + store;
        assert newStore[0] == e;
        assert newStore[1..] == store;
    }

    lemma updateKey(store: seq<StoreEntry>, idx: int, e: StoreEntry, now: Time)
        requires UniqueKeys(store)
        requires 0 <= idx < |store|
        requires e.key == store[idx].key
        requires isLive(e, now)
        ensures e.key in Map(store[idx := e], now)
        ensures Map(store[idx := e], now)[e.key] == e.val
    {
        var newStore := store[idx := e];
        UniqueKeysAfterUpdate(store, idx, e);
        FindIndexAfterUpdate(store, idx, e, e.key);
        assert FindIndex(newStore, e.key) == idx;
        assert newStore[idx] == e;
        assert isLive(newStore[FindIndex(newStore, e.key)], now);
        isInMap(newStore, e.key, now);
    }

    lemma appendKey(store: seq<StoreEntry>, e: StoreEntry, now: Time)
        requires UniqueKeys(store)
        requires FindIndex(store, e.key) == -1
        requires isLive(e, now)
        ensures e.key in Map(store + [e], now)
        ensures Map(store + [e], now)[e.key] == e.val
    {
        var newStore := store + [e];
        UniqueKeysAfterAppend(store, e);
        FindIndexAfterAppend(store, e, e.key);
        assert FindIndex(newStore, e.key) == |store|;
        assert newStore[|store|] == e;
        isInMap(newStore, e.key, now);
    }

    lemma removeKey(store: seq<StoreEntry>, idx: int, now: Time)
        requires UniqueKeys(store)
        requires 0 <= idx < |store|
        ensures store[idx].key !in Map(seqRemove(store, idx), now)
    {
        var k := store[idx].key;
        var newStore := seqRemove(store, idx);
        UniqueKeysAfterRemove(store, idx);
        assert FindIndex(newStore, k) == -1;
        notInMap(newStore, k, now);
    }
}

module CacheImpl {
    import opened Types
    import opened Abstraction
    import opened Helpers

    class Cache {
        var store: seq<StoreEntry>

        ghost predicate Valid()
            reads this
        {
            UniqueKeys(store)
        }

        ghost function view(now: Time): map<Key, Value>
            reads this
            requires Valid()
        {
            Map(store, now)
        }

        constructor()
            ensures store == []
            ensures Valid()
            ensures forall now: Time :: view(now) == map[]
        {
            store := [];
        }

        method Get(k: Key, now: Time) returns (result: Option<Value>)
            requires Valid()
            ensures Valid()
            ensures result.Some? <==> k in view(now)
            ensures result.Some? ==> result.value == view(now)[k]
            ensures store == old(store)
        {
            var idx := ScanForKey(k);
            inMapIff(store, k, now);
            if idx >= 0 && isLive(store[idx], now) {
                isInMap(store, k, now);
                result := Some(store[idx].val);
            } else {
                notInMap(store, k, now);
                result := None;
            }
        }

        method ScanForKey(k: Key) returns (idx: int)
            requires Valid()
            ensures idx == FindIndex(store, k)
            ensures -1 <= idx < |store|
            ensures idx >= 0 ==> store[idx].key == k
            ensures idx == -1 ==> forall i :: 0 <= i < |store| ==> store[i].key != k
        {
            idx := 0;
            while idx < |store|
                invariant 0 <= idx <= |store|
                invariant forall i :: 0 <= i < idx ==> store[i].key != k
            {
                if store[idx].key == k {
                    return idx;
                }
                idx := idx + 1;
            }
            idx := -1;
        }

        method Set(k: Key, v: Value, ttl: Time, now: Time)
            requires ttl > 0
            requires Valid()
            modifies this
            ensures Valid()
            ensures k in view(now)
            ensures view(now)[k] == v
            ensures forall other: Key :: other != k ==>
                ((other in view(now)) == (other in old(view(now)))) &&
                (other in old(view(now)) ==> view(now)[other] == old(view(now))[other])
        {
            var entry := StoreEntry(k, v, now + ttl);
            ghost var oldStore := store;
            ghost var oldView := view(now);
            
            var i := 0;
            var found := false;
            var foundIdx := -1;
            
            while i < |store|
                invariant 0 <= i <= |store|
                invariant foundIdx == -1 || (0 <= foundIdx < i && store[foundIdx].key == k)
                invariant !found <==> foundIdx == -1
                invariant found <==> (foundIdx >= 0 && store[foundIdx].key == k)
                invariant foundIdx == -1 ==> forall j :: 0 <= j < i ==> store[j].key != k
                invariant store == oldStore
                invariant Valid()
            {
                if store[i].key == k {
                    found := true;
                    foundIdx := i;
                    break;
                }
                i := i + 1;
            }
            
            // found <==> key exists in store
            assert found <==> FindIndex(store, k) >= 0;
            assert found ==> foundIdx == FindIndex(store, k);
            
            if found {
                // Update existing entry - build new store with loop
                var newStore: seq<StoreEntry> := [];
                var j := 0;
                
                while j < |store|
                    invariant 0 <= j <= |store|
                    invariant |newStore| == j
                    invariant forall m :: 0 <= m < j ==> 
                        newStore[m] == (if m == foundIdx then entry else store[m])
                    invariant forall m, n :: 0 <= m < n < |newStore| ==> newStore[m].key != newStore[n].key
                {
                    if j == foundIdx {
                        newStore := newStore + [entry];
                    } else {
                        newStore := newStore + [store[j]];
                    }
                    j := j + 1;
                }
                
                assert newStore == store[foundIdx := entry];
                store := newStore;
                
                assert isLive(store[foundIdx], now);
                updateKey(oldStore, foundIdx, entry, now);
                
                forall other: Key | other != k
                    ensures (other in view(now)) == (other in Map(oldStore, now))
                    ensures other in Map(oldStore, now) ==> view(now)[other] == Map(oldStore, now)[other]
                {
                    updateKeyOthersIntact(oldStore, foundIdx, entry, other, now);
                }
            } else {
                // Append new entry
                store := store + [entry];
                assert isLive(store[|store|-1], now);
                appendKey(oldStore, entry, now);
                
                forall other: Key | other != k
                    ensures (other in view(now)) == (other in Map(oldStore, now))
                    ensures other in Map(oldStore, now) ==> view(now)[other] == Map(oldStore, now)[other]
                {
                    appendKeyOthersIntact(oldStore, entry, other, now);
                }
            }
        }

        method Add(k: Key, v: Value, ttl: Time, now: Time) returns (success: bool)
            requires ttl > 0
            requires Valid()
            modifies this
            ensures Valid()
            ensures success <==> k !in old(view(now))
            ensures success ==> k in view(now) && view(now)[k] == v
            ensures !success ==> view(now) == old(view(now))
            ensures forall other: Key :: other != k ==>
                ((other in view(now)) == (other in old(view(now)))) &&
                (other in old(view(now)) ==> view(now)[other] == old(view(now))[other])
            ensures !success ==> store == old(store)
        {
            var idx := ScanForKey(k);
            inMapIff(store, k, now);
            
            if idx >= 0 && isLive(store[idx], now) {
                // Key exists and is live - cannot add
                success := false;
            } else {
                var entry := StoreEntry(k, v, now + ttl);
                ghost var oldStore := store;
                
                if idx >= 0 {
                    // Key exists but expired - update using sequence update
                    store := store[idx := entry];
                    updateKey(oldStore, idx, entry, now);
                    forall other: Key | other != k
                        ensures (other in view(now)) == (other in Map(oldStore, now))
                        ensures other in Map(oldStore, now) ==> view(now)[other] == Map(oldStore, now)[other]
                    {
                        updateKeyOthersIntact(oldStore, idx, entry, other, now);
                    }
                } else {
                    // Key doesn't exist - append
                    store := store + [entry];
                    appendKey(oldStore, entry, now);
                    forall other: Key | other != k
                        ensures (other in view(now)) == (other in Map(oldStore, now))
                        ensures other in Map(oldStore, now) ==> view(now)[other] == Map(oldStore, now)[other]
                    {
                        appendKeyOthersIntact(oldStore, entry, other, now);
                    }
                }
                success := true;
            }
        }

        method Replace(k: Key, v: Value, ttl: Time, now: Time) returns (success: bool)
            requires ttl > 0
            requires Valid()
            modifies this
            ensures Valid()
            ensures success <==> k in old(view(now))
            ensures success ==> k in view(now) && view(now)[k] == v
            ensures !success ==> view(now) == old(view(now))
            ensures forall other: Key :: other != k ==>
                ((other in view(now)) == (other in old(view(now)))) &&
                (other in old(view(now)) ==> view(now)[other] == old(view(now))[other])
            ensures !success ==> store == old(store)
        {
            // Functional approach: use ScanForKey helper
            var idx := ScanForKey(k);
            inMapIff(store, k, now);
            
            if idx >= 0 && isLive(store[idx], now) {
                // Key exists and is live - replace using sequence update
                var entry := StoreEntry(k, v, now + ttl);
                ghost var oldStore := store;
                store := store[idx := entry];
                updateKey(oldStore, idx, entry, now);
                forall other: Key | other != k
                    ensures (other in view(now)) == (other in Map(oldStore, now))
                    ensures other in Map(oldStore, now) ==> view(now)[other] == Map(oldStore, now)[other]
                {
                    updateKeyOthersIntact(oldStore, idx, entry, other, now);
                }
                success := true;
            } else {
                success := false;
            }
        }

        method Delete(k: Key, now: Time) returns (found: bool)
            requires Valid()
            modifies this
            ensures Valid()
            ensures found <==> k in old(view(now))
            ensures k !in view(now)
            ensures forall other: Key :: other != k ==>
                ((other in view(now)) == (other in old(view(now)))) &&
                (other in old(view(now)) ==> view(now)[other] == old(view(now))[other])
        {
            // Functional approach: use ScanForKey helper and seqRemove function
            var idx := ScanForKey(k);
            inMapIff(store, k, now);
            found := idx >= 0 && isLive(store[idx], now);
            
            if idx >= 0 {
                ghost var oldStore := store;
                store := seqRemove(store, idx);
                removeKey(oldStore, idx, now);
                forall other: Key | other != k
                    ensures (other in view(now)) == (other in Map(oldStore, now))
                    ensures other in Map(oldStore, now) ==> view(now)[other] == Map(oldStore, now)[other]
                {
                    removeKeyOthersIntact(oldStore, idx, other, now);
                }
            } else {
                notInMap(store, k, now);
            }
        }
    }
}

module Commands {
    import opened Types
    import opened CacheImpl

    datatype Command = 
        | CmdGet(key: Key)
        | CmdSet(key: Key, value: Value, ttl: Time)
        | CmdAdd(key: Key, value: Value, ttl: Time)
        | CmdReplace(key: Key, value: Value, ttl: Time)
        | CmdDelete(key: Key)
        | CmdInvalid

    datatype Response =
        | RespValue(value: Value)
        | RespNotFound
        | RespStored
        | RespNotStored
        | RespDeleted
        | RespError(msg: string)

    predicate IsDigit(c: char)
    {
        '0' <= c <= '9'
    }

    function CharToDigit(c: char): int
        requires IsDigit(c)
    {
        (c as int) - ('0' as int)
    }

    function Pow10(n: nat): int
    {
        if n == 0 then 1 else 10 * Pow10(n - 1)
    }

    predicate AllDigits(s: string)
    {
        forall i :: 0 <= i < |s| ==> IsDigit(s[i])
    }

    function ParseDigits(s: string): int
        requires AllDigits(s)
        requires |s| > 0
        decreases |s|
    {
        if |s| == 1 then CharToDigit(s[0])
        else ParseDigits(s[..|s|-1]) * 10 + CharToDigit(s[|s|-1])
    }

    function ParseInt(s: string): (bool, int)
    {
        if |s| == 0 then (false, 0)
        else if s[0] == '-' then
            if |s| > 1 && AllDigits(s[1..]) then (true, -ParseDigits(s[1..]))
            else (false, 0)
        else if AllDigits(s) then (true, ParseDigits(s))
        else (false, 0)
    }

    function FindSpace(s: string, start: nat): nat
        requires start <= |s|
        ensures start <= FindSpace(s, start) <= |s|
        decreases |s| - start
    {
        if start >= |s| then |s|
        else if s[start] == ' ' then start
        else FindSpace(s, start + 1)
    }

    function SplitHelper(s: string, start: nat, acc: seq<string>): seq<string>
        requires start <= |s|
        decreases |s| - start
    {
        if start >= |s| then acc
        else if s[start] == ' ' then SplitHelper(s, start + 1, acc)
        else 
            var endPos := FindSpace(s, start);
            SplitHelper(s, endPos, acc + [s[start..endPos]])
    }

    function Split(s: string): seq<string>
    {
        SplitHelper(s, 0, [])
    }

    predicate StrEq(a: string, b: string)
    {
        a == b
    }

    function ParseCommand(input: string): Command
    {
        var tokens := Split(input);
        if |tokens| == 0 then CmdInvalid
        else if StrEq(tokens[0], "get") && |tokens| == 2 then
            var (ok, key) := ParseInt(tokens[1]);
            if ok then CmdGet(key) else CmdInvalid
        else if StrEq(tokens[0], "set") && |tokens| == 4 then
            var (ok1, key) := ParseInt(tokens[1]);
            var (ok2, val) := ParseInt(tokens[2]);
            var (ok3, ttl) := ParseInt(tokens[3]);
            if ok1 && ok2 && ok3 && ttl > 0 then CmdSet(key, val, ttl) else CmdInvalid
        else if StrEq(tokens[0], "add") && |tokens| == 4 then
            var (ok1, key) := ParseInt(tokens[1]);
            var (ok2, val) := ParseInt(tokens[2]);
            var (ok3, ttl) := ParseInt(tokens[3]);
            if ok1 && ok2 && ok3 && ttl > 0 then CmdAdd(key, val, ttl) else CmdInvalid
        else if StrEq(tokens[0], "replace") && |tokens| == 4 then
            var (ok1, key) := ParseInt(tokens[1]);
            var (ok2, val) := ParseInt(tokens[2]);
            var (ok3, ttl) := ParseInt(tokens[3]);
            if ok1 && ok2 && ok3 && ttl > 0 then CmdReplace(key, val, ttl) else CmdInvalid
        else if StrEq(tokens[0], "delete") && |tokens| == 2 then
            var (ok, key) := ParseInt(tokens[1]);
            if ok then CmdDelete(key) else CmdInvalid
        else CmdInvalid
    }

    // Check if command has valid TTL
    predicate ValidCmd(cmd: Command)
    {
        match cmd {
            case CmdGet(_) => true
            case CmdSet(_, _, ttl) => ttl > 0
            case CmdAdd(_, _, ttl) => ttl > 0
            case CmdReplace(_, _, ttl) => ttl > 0
            case CmdDelete(_) => true
            case CmdInvalid => true
        }
    }

    method Execute(cache: Cache, cmd: Command, now: Time) returns (resp: Response)
        requires ValidCmd(cmd)
        requires cache.Valid()
        modifies cache
        ensures cache.Valid()
        ensures cmd.CmdInvalid? ==> resp.RespError?
        ensures cmd.CmdSet? ==> resp == RespStored
        ensures cmd.CmdDelete? ==> resp == RespDeleted
    {
        match cmd {
            case CmdGet(key) =>
                var result := cache.Get(key, now);
                resp := if result.Some? then RespValue(result.value) else RespNotFound;
            case CmdSet(key, val, ttl) =>
                cache.Set(key, val, ttl, now);
                resp := RespStored;
            case CmdAdd(key, val, ttl) =>
                var success := cache.Add(key, val, ttl, now);
                resp := if success then RespStored else RespNotStored;
            case CmdReplace(key, val, ttl) =>
                var success := cache.Replace(key, val, ttl, now);
                resp := if success then RespStored else RespNotStored;
            case CmdDelete(key) =>
                var _ := cache.Delete(key, now);
                resp := RespDeleted;
            case CmdInvalid =>
                resp := RespError("Invalid command");
        }
    }

    function DigitToChar(d: int): char
        requires 0 <= d < 10
    {
        ('0' as int + d) as char
    }

    function NatToString(n: int): string
        requires n >= 0
        decreases n
    {
        if n < 10 then [DigitToChar(n)]
        else NatToString(n / 10) + [DigitToChar(n % 10)]
    }

    function IntToString(n: int): string
    {
        if n < 0 then "-" + NatToString(-n)
        else NatToString(n)
    }

    function FormatResponse(resp: Response): string
    {
        match resp {
            case RespValue(v) => "VALUE " + IntToString(v)
            case RespNotFound => "NOT_FOUND"
            case RespStored => "STORED"
            case RespNotStored => "NOT_STORED"
            case RespDeleted => "DELETED"
            case RespError(msg) => "ERROR " + msg
        }
    }

    // ParseCommand always returns a valid command (TTL > 0 when needed)
    lemma ParseCommandValid(input: string)
        ensures ValidCmd(ParseCommand(input))
    {
        var tokens := Split(input);
        if |tokens| == 0 {
        } else if StrEq(tokens[0], "get") && |tokens| == 2 {
        } else if StrEq(tokens[0], "set") && |tokens| == 4 {
            var (ok1, key) := ParseInt(tokens[1]);
            var (ok2, val) := ParseInt(tokens[2]);
            var (ok3, ttl) := ParseInt(tokens[3]);
        } else if StrEq(tokens[0], "add") && |tokens| == 4 {
            var (ok1, key) := ParseInt(tokens[1]);
            var (ok2, val) := ParseInt(tokens[2]);
            var (ok3, ttl) := ParseInt(tokens[3]);
        } else if StrEq(tokens[0], "replace") && |tokens| == 4 {
            var (ok1, key) := ParseInt(tokens[1]);
            var (ok2, val) := ParseInt(tokens[2]);
            var (ok3, ttl) := ParseInt(tokens[3]);
        } else if StrEq(tokens[0], "delete") && |tokens| == 2 {
        } else {
        }
    }

    // parse, execute, format
    method ProcessCommand(cache: Cache, input: string, now: Time) returns (output: string)
        requires cache.Valid()
        modifies cache
        ensures cache.Valid()
    {
        var cmd := ParseCommand(input);
        ParseCommandValid(input);
        var resp := Execute(cache, cmd, now);
        output := FormatResponse(resp);
    }
}

module CommandTests {
    import opened Types
    import opened CacheImpl
    import opened Commands

    // Test that Execute terminates and returns appropriate response types
    method TestExecuteCommands()
    {
        var cache := new Cache();
        assert cache.Valid();
        
        // Set always stores
        var resp := Execute(cache, CmdSet(1, 42, 50), 100);
        
        // Get can return value or not found
        resp := Execute(cache, CmdGet(1), 100);
        
        // Add can succeed or fail
        resp := Execute(cache, CmdAdd(2, 100, 50), 100);
        
        // Replace can succeed or fail
        resp := Execute(cache, CmdReplace(1, 99, 50), 100);
        
        // Delete always returns Deleted
        resp := Execute(cache, CmdDelete(1), 100);
        
        // Invalid returns error
        resp := Execute(cache, CmdInvalid, 100);
        assert resp.RespError?;
    }

    // Verify parsing produces valid commands
    method TestParseValid()
    {
        ParseCommandValid("get 1");
        ParseCommandValid("set 1 2 3");
        ParseCommandValid("add 1 2 3");
        ParseCommandValid("replace 1 2 3");
        ParseCommandValid("delete 1");
        ParseCommandValid("invalid");
    }
}

method Main()
{
    var cache := new CacheImpl.Cache();
    var now := 0;

    print "[ Memcache ]";

    print "> set 1 100 60\n";
    var out := Commands.ProcessCommand(cache, "set 1 100 60", now);
    print out, "\n\n";

    print "> set 2 200 60\n";
    out := Commands.ProcessCommand(cache, "set 2 200 60", now);
    print out, "\n\n";

    print "> get 1\n";
    out := Commands.ProcessCommand(cache, "get 1", now);
    print out, "\n\n";

    print "> get 2\n";
    out := Commands.ProcessCommand(cache, "get 2", now);
    print out, "\n\n";

    print "> get 999\n";
    out := Commands.ProcessCommand(cache, "get 999", now);
    print out, "\n\n";

    print "> add 1 999 60\n";
    out := Commands.ProcessCommand(cache, "add 1 999 60", now);
    print out, " (key 1 already exists)\n\n";

    print "> add 3 300 60\n";
    out := Commands.ProcessCommand(cache, "add 3 300 60", now);
    print out, "\n\n";

    print "> replace 1 111 60\n";
    out := Commands.ProcessCommand(cache, "replace 1 111 60", now);
    print out, "\n\n";

    print "> get 1\n";
    out := Commands.ProcessCommand(cache, "get 1", now);
    print out, "\n\n";

    print "> replace 999 0 60\n";
    out := Commands.ProcessCommand(cache, "replace 999 0 60", now);
    print out, " (key 999 doesn't exist)\n\n";

    print "> delete 2\n";
    out := Commands.ProcessCommand(cache, "delete 2", now);
    print out, "\n\n";

    print "> get 2\n";
    out := Commands.ProcessCommand(cache, "get 2", now);
    print out, "\n\n";

    print "> invalid command\n";
    out := Commands.ProcessCommand(cache, "invalid command", now);
    print out, "\n\n";

    print "Demo complete!\n";
}
