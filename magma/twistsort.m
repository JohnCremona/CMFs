Attach("utils.m"); Attach("mfutils.m");
cmp := func<a,b|(c ne 0 select c else CompareEmbeddedNewformLabels(a[2],b[2])) where c:=CompareEmbeddedNewformLabels(a[1],b[1])>;
putrecs(file,Sort(getrecs(file),cmp);
exit;
