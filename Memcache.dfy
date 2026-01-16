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

    function mapRemove(m: map<Key, Entry>, k: Key): map<Key, Entry>
    {
        map k' | k' in m && k' != k :: m[k']
    }

    lemma removeKeyOthersIntact(store: map<Key, Entry>, k: Key, other: Key, now: Time)
        requires k in store
        requires k != other
        ensures (other in Map(mapRemove(store, k), now)) == (other in Map(store, now))
        ensures other in Map(store, now) ==> Map(mapRemove(store, k), now)[other] == Map(store, now)[other]
    {
        var newStore := mapRemove(store, k);
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
        ensures k !in Map(mapRemove(store, k), now)
    {
        var newStore := mapRemove(store, k);
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
                store := mapRemove(store, k);
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
        modifies cache
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
        modifies cache
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
