module Types {
    type Key = int
    type Value = int
    type Time = int

    datatype Entry = Entry(val: Value, exp: Time)
    datatype Option<T> = None | Some(value: T)

    predicate isLive(e: Entry, now: Time)
    {
        e.exp > now
    }

    predicate keyLive(store: map<Key, Entry>, k: Key, now: Time)
    {
        k in store && isLive(store[k], now)
    }

    predicate keyDead(store: map<Key, Entry>, k: Key, now: Time)
    {
        k !in store || !isLive(store[k], now)
    }
}

module Abstraction {
    import opened Types

    ghost function setToSeq(s: set<Key>): seq<Key>
        ensures forall k :: k in s <==> k in setToSeq(s)
        ensures |setToSeq(s)| == |s|
    {
        if s == {} then
            []
        else
            var x :| x in s;
            [x] + setToSeq(s - {x})
    }

    ghost function MapHelper(store: map<Key, Entry>, keys: seq<Key>, now: Time): map<Key, Value>
        decreases |keys|
    {
        if |keys| == 0 then
            map[]
        else
            var k := keys[0];
            var rest := MapHelper(store, keys[1..], now);
            if k in store && isLive(store[k], now) then
                rest[k := store[k].val]
            else
                rest
    }

    ghost function Map(store: map<Key, Entry>, now: Time): map<Key, Value>
    {
        MapHelper(store, setToSeq(store.Keys), now)
    }

    lemma isInMap(store: map<Key, Entry>, k: Key, now: Time)
        requires k in store
        requires isLive(store[k], now)
        ensures k in Map(store, now)
        ensures Map(store, now)[k] == store[k].val
    {
        var keys := setToSeq(store.Keys);
        isInMapHelper(store, keys, k, now);
    }

    lemma isInMapHelper(store: map<Key, Entry>, keys: seq<Key>, k: Key, now: Time)
        requires k in keys
        requires k in store
        requires isLive(store[k], now)
        ensures k in MapHelper(store, keys, now)
        ensures MapHelper(store, keys, now)[k] == store[k].val
        decreases |keys|
    {
        if |keys| == 0 {
            assert false;
        } else if keys[0] == k {
            var rest := MapHelper(store, keys[1..], now);
        } else {
            assert k in keys[1..];
            isInMapHelper(store, keys[1..], k, now);
        }
    }

    lemma notInMap(store: map<Key, Entry>, k: Key, now: Time)
        requires k !in store || !isLive(store[k], now)
        ensures k !in Map(store, now)
    {
        var keys := setToSeq(store.Keys);
        notInMapHelper(store, keys, k, now);
    }

    lemma notInMapHelper(store: map<Key, Entry>, keys: seq<Key>, k: Key, now: Time)
        requires k !in store || !isLive(store[k], now)
        ensures k !in MapHelper(store, keys, now)
        decreases |keys|
    {
        if |keys| == 0 {
        } else {
            var first := keys[0];
            var rest := MapHelper(store, keys[1..], now);
            notInMapHelper(store, keys[1..], k, now);
            if first in store && isLive(store[first], now) {
                if first == k {
                    assert false;
                }
            }
        }
    }

    lemma inMapIff(store: map<Key, Entry>, k: Key, now: Time)
        ensures k in Map(store, now) <==> (k in store && isLive(store[k], now))
    {
        if k in store && isLive(store[k], now) {
            isInMap(store, k, now);
        } else {
            notInMap(store, k, now);
        }
    }
}

module Helpers {
    import opened Types
    import opened Abstraction

    lemma updateKeyOthersIntact(store: map<Key, Entry>, k: Key, e: Entry, other: Key, now: Time)
        requires k != other
        ensures (other in Map(store[k := e], now)) == (other in Map(store, now))
        ensures other in Map(store, now) ==> Map(store[k := e], now)[other] == Map(store, now)[other]
    {
        var newStore := store[k := e];
        assert (other in store && isLive(store[other], now)) == 
               (other in newStore && isLive(newStore[other], now));
        inMapIff(store, other, now);
        inMapIff(newStore, other, now);
        if other in Map(store, now) {
            isInMap(store, other, now);
            isInMap(newStore, other, now);
        }
    }

    lemma removeKeyOthersIntact(store: map<Key, Entry>, k: Key, other: Key, now: Time)
        requires k in store
        requires k != other
        ensures (other in Map(store - {k}, now)) == (other in Map(store, now))
        ensures other in Map(store, now) ==> Map(store - {k}, now)[other] == Map(store, now)[other]
    {
        var newStore := store - {k};
        inMapIff(store, other, now);
        inMapIff(newStore, other, now);
        if other in Map(store, now) {
            isInMap(store, other, now);
            isInMap(newStore, other, now);
        }
    }

    lemma updateKey(store: map<Key, Entry>, k: Key, e: Entry, now: Time)
        requires isLive(e, now)
        ensures k in Map(store[k := e], now)
        ensures Map(store[k := e], now)[k] == e.val
    {
        var newStore := store[k := e];
        assert k in newStore;
        assert isLive(newStore[k], now);
        isInMap(newStore, k, now);
    }

    lemma removeKey(store: map<Key, Entry>, k: Key, now: Time)
        requires k in store
        ensures k !in Map(store - {k}, now)
    {
        var newStore := store - {k};
        assert k !in newStore;
        notInMap(newStore, k, now);
    }
}

module CacheImpl {
    import opened Types
    import opened Abstraction
    import opened Helpers

    class Cache {
        var store: map<Key, Entry>

        ghost function view(now: Time): map<Key, Value>
            reads this
        {
            Map(store, now)
        }

        constructor()
            ensures store == map[]
            ensures forall now: Time :: view(now) == map[]
        {
            store := map[];
        }

        method Get(k: Key, now: Time) returns (result: Option<Value>)
            ensures result.Some? <==> k in view(now)
            ensures result.Some? ==> result.value == view(now)[k]
            ensures result.Some? ==> k in store
            ensures result.Some? ==> result.value == store[k].val
            ensures store == old(store)
        {
            inMapIff(store, k, now);
            if k in store && isLive(store[k], now) {
                isInMap(store, k, now);
                result := Some(store[k].val);
            } else {
                notInMap(store, k, now);
                result := None;
            }
        }

        method Set(k: Key, v: Value, ttl: Time, now: Time)
            requires ttl > 0
            modifies this
            ensures k in view(now)
            ensures view(now)[k] == v
            ensures forall other: Key :: other != k ==>
                ((other in view(now)) == (other in old(view(now)))) &&
                (other in old(view(now)) ==> view(now)[other] == old(view(now))[other])
            ensures k in store
            ensures store[k].val == v
            ensures store[k].exp == now + ttl
            ensures forall other: Key :: other != k ==>
                (other in store <==> other in old(store)) &&
                (other in old(store) ==> store[other] == old(store)[other])
        {
            var entry := Entry(v, now + ttl);
            ghost var oldStore := store;
            store := store[k := entry];
            
            assert isLive(store[k], now);
            updateKey(oldStore, k, entry, now);
            
            forall other: Key | other != k
                ensures (other in view(now)) == (other in Map(oldStore, now))
                ensures other in Map(oldStore, now) ==> view(now)[other] == Map(oldStore, now)[other]
            {
                updateKeyOthersIntact(oldStore, k, entry, other, now);
            }
        }

        method Add(k: Key, v: Value, ttl: Time, now: Time) returns (success: bool)
            requires ttl > 0
            modifies this
            ensures success <==> k !in old(view(now))
            ensures success ==> k in view(now) && view(now)[k] == v
            ensures !success ==> view(now) == old(view(now))
            ensures forall other: Key :: other != k ==>
                ((other in view(now)) == (other in old(view(now)))) &&
                (other in old(view(now)) ==> view(now)[other] == old(view(now))[other])
            ensures success ==> k in store
            ensures success ==> store[k].val == v
            ensures success ==> store[k].exp == now + ttl
            ensures !success ==> store == old(store)
            ensures forall other: Key :: other != k ==>
                (other in store <==> other in old(store)) &&
                (other in old(store) ==> store[other] == old(store)[other])
        {
            inMapIff(store, k, now);
            if k in store && isLive(store[k], now) {
                success := false;
            } else {
                var entry := Entry(v, now + ttl);
                ghost var oldStore := store;
                store := store[k := entry];
                updateKey(oldStore, k, entry, now);
                forall other: Key | other != k
                    ensures (other in view(now)) == (other in Map(oldStore, now))
                    ensures other in Map(oldStore, now) ==> view(now)[other] == Map(oldStore, now)[other]
                {
                    updateKeyOthersIntact(oldStore, k, entry, other, now);
                }
                success := true;
            }
        }

        method Replace(k: Key, v: Value, ttl: Time, now: Time) returns (success: bool)
            requires ttl > 0
            modifies this
            ensures success <==> k in old(view(now))
            ensures success ==> k in view(now) && view(now)[k] == v
            ensures !success ==> view(now) == old(view(now))
            ensures forall other: Key :: other != k ==>
                ((other in view(now)) == (other in old(view(now)))) &&
                (other in old(view(now)) ==> view(now)[other] == old(view(now))[other])
            ensures success ==> k in store
            ensures success ==> store[k].val == v
            ensures success ==> store[k].exp == now + ttl
            ensures !success ==> store == old(store)
            ensures forall other: Key :: other != k ==>
                (other in store <==> other in old(store)) &&
                (other in old(store) ==> store[other] == old(store)[other])
        {
            inMapIff(store, k, now);
            if k in store && isLive(store[k], now) {
                var entry := Entry(v, now + ttl);
                ghost var oldStore := store;
                store := store[k := entry];
                updateKey(oldStore, k, entry, now);
                forall other: Key | other != k
                    ensures (other in view(now)) == (other in Map(oldStore, now))
                    ensures other in Map(oldStore, now) ==> view(now)[other] == Map(oldStore, now)[other]
                {
                    updateKeyOthersIntact(oldStore, k, entry, other, now);
                }
                success := true;
            } else {
                success := false;
            }
        }

        method Delete(k: Key, now: Time) returns (found: bool)
            modifies this
            ensures found <==> k in old(view(now))
            ensures k !in view(now)
            ensures forall other: Key :: other != k ==>
                ((other in view(now)) == (other in old(view(now)))) &&
                (other in old(view(now)) ==> view(now)[other] == old(view(now))[other])
            ensures k !in store
            ensures forall other: Key :: other != k ==>
                (other in store <==> other in old(store)) &&
                (other in old(store) ==> store[other] == old(store)[other])
        {
            inMapIff(store, k, now);
            found := k in store && isLive(store[k], now);
            if k in store {
                ghost var oldStore := store;
                store := store - {k};
                removeKey(oldStore, k, now);
                forall other: Key | other != k
                    ensures (other in view(now)) == (other in Map(oldStore, now))
                    ensures other in Map(oldStore, now) ==> view(now)[other] == Map(oldStore, now)[other]
                {
                    removeKeyOthersIntact(oldStore, k, other, now);
                }
            } else {
                notInMap(store, k, now);
            }
        }
    }
}

// TESTS :3

module Tests {
    import opened Types
    import opened Abstraction
    import opened CacheImpl

    // get tests

    method TestGetEmpty()
    {
        var cache := new Cache();
        var result := cache.Get(1, 100);
        assert result.None?;
        assert cache.store == map[];
    }

    method TestGetLive()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        var result := cache.Get(1, 100);
        assert result.Some? && result.value == 42;
        assert cache.store[1].val == 42;
        assert cache.store[1].exp == 150;
    }

    method TestGetExpired()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        assert cache.store[1].exp == 150;
        assert !isLive(cache.store[1], 200);
        inMapIff(cache.store, 1, 200);
        var result := cache.Get(1, 200);
        assert result.None?;
        assert 1 in cache.store;
        assert cache.store[1].val == 42;
    }

    method TestGetMissing()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        cache.Set(2, 100, 50, 100);
        inMapIff(cache.store, 3, 100);
        var result := cache.Get(3, 100);
        assert result.None?;
        assert cache.store[1].val == 42;
        assert cache.store[2].val == 100;
    }

    // set tests

    method TestSetEmpty()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        assert 1 in cache.store;
        assert cache.store[1].val == 42;
        assert cache.store[1].exp == 150;
        var result := cache.Get(1, 100);
        assert result.Some? && result.value == 42;
    }

    method TestSetOverwrite()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        assert cache.store[1].val == 42;
        cache.Set(1, 99, 100, 100);
        assert cache.store[1].val == 99;
        assert cache.store[1].exp == 200;
        var result := cache.Get(1, 100);
        assert result.Some? && result.value == 99;
    }

    method TestSetExpired()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        assert cache.store[1].exp == 150;
        assert !isLive(cache.store[1], 200);
        cache.Set(1, 99, 50, 200);
        assert cache.store[1].val == 99;
        assert cache.store[1].exp == 250;
        var result := cache.Get(1, 200);
        assert result.Some? && result.value == 99;
    }

    method TestSetPreservesOthers()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        cache.Set(2, 100, 50, 100);
        assert cache.store[1].val == 42;
        assert cache.store[2].val == 100;
        cache.Set(1, 55, 50, 100);
        assert cache.store[1].val == 55;
        assert cache.store[2].val == 100;
        assert cache.store[2].exp == 150;
    }

    // add tests

    method TestAddEmpty()
    {
        var cache := new Cache();
        var success := cache.Add(1, 42, 50, 100);
        assert success;
        assert cache.store[1].val == 42;
        assert cache.store[1].exp == 150;
    }

    method TestAddLiveFails()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        var success := cache.Add(1, 99, 50, 100);
        assert !success;
        assert cache.store[1].val == 42;
        assert cache.store[1].exp == 150;
    }

    method TestAddExpired()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        assert cache.store[1].exp == 150;
        assert !isLive(cache.store[1], 200);
        inMapIff(cache.store, 1, 200);
        var success := cache.Add(1, 99, 50, 200);
        assert success;
        assert cache.store[1].val == 99;
        assert cache.store[1].exp == 250;
    }

    method TestAddNew()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        inMapIff(cache.store, 2, 100);
        var success := cache.Add(2, 100, 50, 100);
        assert success;
        assert cache.store[2].val == 100;
        assert cache.store[1].val == 42;
    }

    method TestAddPreservesOthers()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        cache.Set(2, 100, 50, 100);
        inMapIff(cache.store, 3, 100);
        var success := cache.Add(3, 200, 50, 100);
        assert success;
        assert cache.store[1].val == 42;
        assert cache.store[1].exp == 150;
        assert cache.store[2].val == 100;
        assert cache.store[2].exp == 150;
    }

    // replace tests

    method TestReplaceEmptyFails()
    {
        var cache := new Cache();
        inMapIff(cache.store, 1, 100);
        var success := cache.Replace(1, 42, 50, 100);
        assert !success;
        assert 1 !in cache.store;
    }

    method TestReplaceLive()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        var success := cache.Replace(1, 99, 50, 100);
        assert success;
        assert cache.store[1].val == 99;
        assert cache.store[1].exp == 150;
    }

    method TestReplaceExpiredFails()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        assert cache.store[1].exp == 150;
        assert !isLive(cache.store[1], 200);
        inMapIff(cache.store, 1, 200);
        var success := cache.Replace(1, 99, 50, 200);
        assert !success;
        assert cache.store[1].val == 42;
        assert cache.store[1].exp == 150;
    }

    method TestReplaceMissingFails()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        inMapIff(cache.store, 2, 100);
        var success := cache.Replace(2, 99, 50, 100);
        assert !success;
        assert 2 !in cache.store;
        assert cache.store[1].val == 42;
    }

    method TestReplacePreservesOthers()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        cache.Set(2, 100, 50, 100);
        var success := cache.Replace(1, 55, 50, 100);
        assert success;
        assert cache.store[1].val == 55;
        assert cache.store[2].val == 100;
        assert cache.store[2].exp == 150;
    }

    // delete tests

    method TestDeleteEmpty()
    {
        var cache := new Cache();
        inMapIff(cache.store, 1, 100);
        var found := cache.Delete(1, 100);
        assert !found;
        assert 1 !in cache.store;
    }

    method TestDeleteLive()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        assert 1 in cache.store;
        var found := cache.Delete(1, 100);
        assert found;
        assert 1 !in cache.store;
        var result := cache.Get(1, 100);
        assert result.None?;
    }

    method TestDeleteExpired()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        assert cache.store[1].exp == 150;
        assert !isLive(cache.store[1], 200);
        inMapIff(cache.store, 1, 200);
        var found := cache.Delete(1, 200);
        assert !found;
        assert 1 !in cache.store;
    }

    method TestDeleteMissing()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        inMapIff(cache.store, 2, 100);
        var found := cache.Delete(2, 100);
        assert !found;
        assert 2 !in cache.store;
        assert cache.store[1].val == 42;
    }

    method TestDeletePreservesOthers()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        cache.Set(2, 100, 50, 100);
        cache.Set(3, 200, 50, 100);
        var found := cache.Delete(2, 100);
        assert found;
        assert 2 !in cache.store;
        assert cache.store[1].val == 42;
        assert cache.store[1].exp == 150;
        assert cache.store[3].val == 200;
        assert cache.store[3].exp == 150;
    }

    // ttl edge cases

    method TestTtlExact()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        assert cache.store[1].exp == 150;
        // at exactly 150 its expired since exp > now not >=
        assert !(cache.store[1].exp > 150);
        assert !isLive(cache.store[1], 150);
        inMapIff(cache.store, 1, 150);
        var result := cache.Get(1, 150);
        assert result.None?;
    }

    method TestTtlBefore()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        assert cache.store[1].exp == 150;
        assert cache.store[1].exp > 149;
        assert isLive(cache.store[1], 149);
        inMapIff(cache.store, 1, 149);
        var result := cache.Get(1, 149);
        assert result.Some? && result.value == 42;
    }

    method TestTtlAfter()
    {
        var cache := new Cache();
        cache.Set(1, 42, 50, 100);
        assert cache.store[1].exp == 150;
        assert !(cache.store[1].exp > 151);
        assert !isLive(cache.store[1], 151);
        inMapIff(cache.store, 1, 151);
        var result := cache.Get(1, 151);
        assert result.None?;
    }

    method TestTtlMin()
    {
        var cache := new Cache();
        cache.Set(1, 42, 1, 100);
        assert cache.store[1].exp == 101;
        assert isLive(cache.store[1], 100);
        var result := cache.Get(1, 100);
        assert result.Some?;
        assert !isLive(cache.store[1], 101);
        inMapIff(cache.store, 1, 101);
        result := cache.Get(1, 101);
        assert result.None?;
    }

    // multi key tests

    method TestMultiKeyExpiry()
    {
        var cache := new Cache();
        cache.Set(1, 10, 50, 100);
        cache.Set(2, 20, 100, 100);
        cache.Set(3, 30, 150, 100);

        assert cache.store[1].exp == 150;
        assert cache.store[2].exp == 200;
        assert cache.store[3].exp == 250;
        assert cache.store[1].val == 10;
        assert cache.store[2].val == 20;
        assert cache.store[3].val == 30;

        // at 175 key 1 expired keys 2 3 live
        assert !isLive(cache.store[1], 175);
        assert isLive(cache.store[2], 175);
        assert isLive(cache.store[3], 175);

        inMapIff(cache.store, 1, 175);
        inMapIff(cache.store, 2, 175);
        inMapIff(cache.store, 3, 175);

        var r1 := cache.Get(1, 175);
        assert r1.None?;
        assert cache.store[2].val == 20;
        assert cache.store[3].val == 30;

        var r2 := cache.Get(2, 175);
        assert r2.Some? && r2.value == 20;
        assert cache.store[3].val == 30;

        var r3 := cache.Get(3, 175);
        assert r3.Some? && r3.value == 30;

        // at 225 keys 1 2 expired key 3 live
        assert !isLive(cache.store[1], 225);
        assert !isLive(cache.store[2], 225);
        assert isLive(cache.store[3], 225);

        inMapIff(cache.store, 1, 225);
        inMapIff(cache.store, 2, 225);
        inMapIff(cache.store, 3, 225);

        r1 := cache.Get(1, 225);
        assert r1.None?;

        r2 := cache.Get(2, 225);
        assert r2.None?;

        assert cache.store[3].val == 30;
        r3 := cache.Get(3, 225);
        assert r3.Some? && r3.value == 30;
    }

    method TestOpsPreserveOthers()
    {
        var cache := new Cache();
        cache.Set(1, 10, 50, 100);
        cache.Set(2, 20, 50, 100);
        cache.Set(3, 30, 50, 100);

        ghost var e2 := cache.store[2];
        ghost var e3 := cache.store[3];

        cache.Set(1, 15, 50, 100);
        assert cache.store[2] == e2;
        assert cache.store[3] == e3;

        var _ := cache.Replace(1, 16, 50, 100);
        assert cache.store[2] == e2;
        assert cache.store[3] == e3;

        var _ := cache.Delete(1, 100);
        assert cache.store[2] == e2;
        assert cache.store[3] == e3;

        assert 1 !in cache.store;
        assert cache.store[2].val == 20;
        assert cache.store[3].val == 30;
    }

    // full scenario

    method TestScenario()
    {
        var cache := new Cache();

        cache.Set(1, 100, 10, 0);
        cache.Set(2, 200, 20, 0);
        cache.Set(3, 300, 30, 0);

        assert cache.store[1].val == 100;
        assert cache.store[1].exp == 10;
        assert cache.store[2].val == 200;
        assert cache.store[2].exp == 20;
        assert cache.store[3].val == 300;
        assert cache.store[3].exp == 30;

        // at 5 all live
        assert isLive(cache.store[1], 5);
        assert isLive(cache.store[2], 5);
        assert isLive(cache.store[3], 5);

        inMapIff(cache.store, 1, 5);
        var result := cache.Get(1, 5);
        assert result.Some? && result.value == 100;

        assert cache.store[2].val == 200;
        inMapIff(cache.store, 2, 5);
        result := cache.Get(2, 5);
        assert result.Some? && result.value == 200;

        assert cache.store[3].val == 300;
        inMapIff(cache.store, 3, 5);
        result := cache.Get(3, 5);
        assert result.Some? && result.value == 300;

        // at 15 key 1 expired
        assert !isLive(cache.store[1], 15);
        assert isLive(cache.store[2], 15);
        assert isLive(cache.store[3], 15);

        inMapIff(cache.store, 1, 15);
        result := cache.Get(1, 15);
        assert result.None?;

        // add succeeds on expired key 1
        var success := cache.Add(1, 111, 50, 15);
        assert success;
        assert cache.store[1].val == 111;
        assert cache.store[1].exp == 65;

        // replace fails on expired key 2 at 25
        assert !isLive(cache.store[2], 25);
        inMapIff(cache.store, 2, 25);
        success := cache.Replace(2, 222, 50, 25);
        assert !success;

        // set works on expired key 2
        cache.Set(2, 222, 50, 25);
        assert cache.store[2].val == 222;
        assert cache.store[2].exp == 75;

        // delete key 3 at 30 when expired
        assert !isLive(cache.store[3], 30);
        inMapIff(cache.store, 3, 30);
        var found := cache.Delete(3, 30);
        assert !found;
        assert 3 !in cache.store;

        // at 50 keys 1 2 live key 3 gone
        assert isLive(cache.store[1], 50);
        assert isLive(cache.store[2], 50);
        assert 3 !in cache.store;

        inMapIff(cache.store, 1, 50);
        result := cache.Get(1, 50);
        assert result.Some? && result.value == 111;

        assert cache.store[2].val == 222;
        inMapIff(cache.store, 2, 50);
        result := cache.Get(2, 50);
        assert result.Some? && result.value == 222;
    }
}
