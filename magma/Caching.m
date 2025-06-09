class_nos := NewStore();
traces_eis := NewStore();
traces_coh := NewStore();

intrinsic CacheClear(name)
{Clear the internal cache}
  // We need to save and restore the id, otherwise horrific things might
  // happen
  StoreClear(name);
  StoreSet(name, "cache", AssociativeArray());
end intrinsic;

procedure SetCache(k,v, name)
  bool, cache := StoreIsDefined(name, "cache");
  if not bool then
    cache := AssociativeArray();
  end if;
  cache[k] := v;
  StoreSet(name, "cache", cache);
end procedure;

function GetCache(k, name)
  bool, cache := StoreIsDefined(name, "cache");
  if not bool then
    cache := AssociativeArray();
    return false, _;
  end if;
  return IsDefined(cache, k);
end function;
