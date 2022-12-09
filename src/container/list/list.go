package list


//@ ghost-parameters: elems set[*Element], list *List
//@ requires e in elems
//@ preserves list.Mem(elems, true)
//@ ensures unfolding list.Mem(elems, true) in e.list == nil || e.next == (&e.list.root) ==> res == nil
//@ ensures unfolding list.Mem(elems, true) in e.list != nil && e.next != (&e.list.root) ==> res == e.next
//@ decreases  
func (e *Element) Next() (res *Element) {
  //@ unfold list.Mem(elems, true)
  defer //@ fold list.Mem(elems, true)
  if p := e.next ; e.list != nil && p != (&e.list.root) {
    return p
  }
  return nil
}

//@ ghost-parameters: elems set[*Element], list *List
//@ requires e in elems
//@ preserves list.Mem(elems, true)
//@ ensures unfolding list.Mem(elems, true) in e.list == nil || e.prev == (&e.list.root) ==> res == nil
//@ ensures unfolding list.Mem(elems, true) in e.list != nil && e.prev != (&e.list.root) ==> res == e.prev
//@ decreases  
func (e *Element) Prev() (res *Element) {
  //@ unfold list.Mem(elems, true)
  defer //@ fold list.Mem(elems, true)
  if p := e.prev ; e.list != nil && p != (&e.list.root) {
    return p
  }
  return nil
}

//@ ghost-parameters: elems set[*Element], isInit bool
//@ requires l.Mem(elems, isInit)
//@ ensures res == l
//@ ensures l.Mem(set[*Element] { &l.root }, true)
//@ ensures unfolding l.Mem(set[*Element] { &l.root }, true) in l.lenT == 0
//@ decreases  
func (l *List) Init() (res *List) {
  //@ unfold l.Mem(elems, isInit)
  l.root.next = &l.root
  l.root.prev = &l.root
  l.lenT = 0
  //@ fold l.Mem(set[*Element] { &l.root }, true)
  return l
}

//@ ensures l.Mem(set[*Element] { &l.root }, true)
//@ ensures unfolding l.Mem(set[*Element] { &l.root }, true) in l.lenT == 0
//@ decreases  
func New() (l *List) {
  l = new(List)
  //@ fold l.Mem(set[*Element] { &l.root }, false)
  l.Init() /*@ with: set[*Element] { &l.root }, false @*/
}

//@ ghost-parameters: elems set[*Element]
//@ pure
//@ requires l.Mem(elems, true)
//@ ensures unfolding l.Mem(elems, true) in res == l.lenT
//@ decreases  
func (l *List) Len() (res int) {
  return (/*@ unfolding: l.Mem(elems, true) @*/ l.lenT)
}

//@ ghost-parameters: elems set[*Element]
//@ preserves acc(l.Mem(elems, true), 1 / 2)
//@ ensures unfolding acc(l.Mem(elems, true), 1 / 2) in (l.lenT == 0 ==> res == nil) && (l.lenT != 0 ==> res == l.root.next)
//@ decreases  
func (l *List) Front() (res *Element) {
  //@ unfold acc(l.Mem(elems, true), 1 / 2)
  defer //@ fold acc(l.Mem(elems, true), 1 / 2)
  if l.lenT == 0 {
    return nil
  }
  return l.root.next
}

//@ ghost-parameters: elems set[*Element]
//@ preserves acc(l.Mem(elems, true), 1 / 2)
//@ ensures unfolding acc(l.Mem(elems, true), 1 / 2) in (l.lenT == 0 ==> res == nil) && (l.lenT != 0 ==> res == l.root.prev)
//@ decreases  
func (l *List) Back() (res *Element) {
  //@ unfold acc(l.Mem(elems, true), 1 / 2)
  defer //@ fold acc(l.Mem(elems, true), 1 / 2)
  if l.lenT == 0 {
    return nil
  }
  return l.root.prev
}

//@ ghost-parameters: elems set[*Element], isInit bool
//@ requires l.Mem(elems, isInit)
//@ ensures l.Mem(elems, true)
//@ ensures isInit ==> unfolding l.Mem(elems, true) in l.lenT == old(unfolding l.Mem(elems, true) in l.lenT)
//@ ensures !isInit ==> unfolding l.Mem(elems, true) in l.lenT == 0
//@ decreases  
func (l *List) lazyInit() () {
  //@ unfold l.Mem(elems, isInit)
  if l.root.next == nil {
    //@ fold l.Mem(elems, isInit)
    l.Init() /*@ with: elems, false @*/
    
  }
  //@ fold l.Mem(elems, true)
}

//@ ghost-parameters: elems set[*Element]
//@ requires l.Mem(elems, true)
//@ requires acc(e)
//@ requires at in elems
//@ requires !e in elems
//@ ensures l.Mem(elems union set[*Element] { e }, true)
//@ ensures unfolding l.Mem(elems union set[*Element] { e }, true) in l.lenT == 1 + old(unfolding l.Mem(elems, true) in l.lenT)
//@ ensures unfolding l.Mem(elems union set[*Element] { e }, true) in at.next == e && e.prev == at
//@ ensures unfolding l.Mem(elems union set[*Element] { e }, true) in old(unfolding l.Mem(elems, true) in at.next).prev == e && e.next == old(unfolding l.Mem(elems, true) in at.next)
//@ ensures res == e
//@ decreases  
func (l *List) insert(e *Element, at *Element) (res *Element) {
  //@ unfold l.Mem(elems, true)
  e.prev = at
  e.next = at.next
  e.prev.next = e
  e.next.prev = e
  e.list = l
  l.lenT += 1
  res = e
  //@ fold l.Mem(elems union set[*Element] { e }, true)
}

//@ ghost-parameters: elems set[*Element]
//@ requires l.Mem(elems, true)
//@ requires at in elems
//@ ensures l.Mem(elems union set[*Element] { res }, true)
//@ ensures unfolding l.Mem(elems union set[*Element] { res }, true) in l.lenT == 1 + old(unfolding l.Mem(elems, true) in l.lenT)
//@ ensures unfolding l.Mem(elems union set[*Element] { res }, true) in at.next == res && res.prev == at
//@ ensures unfolding l.Mem(elems union set[*Element] { res }, true) in old(unfolding l.Mem(elems, true) in at.next).prev == res && res.next == old(unfolding l.Mem(elems, true) in at.next)
//@ decreases  
func (l *List) insertValue(v any, at *Element) (res *Element) {
  res = &Element {Value: v }
  //@ assume !res in elems
  return l.insert(res, at) /*@ with: elems @*/
}

//@ ghost-parameters: elems set[*Element]
//@ requires l.Mem(elems, true)
//@ requires e in elems
//@ requires e != (&l.root)
//@ ensures l.Mem(elems setminus set[*Element] { e }, true)
//@ ensures !e in elems setminus set[*Element] { e }
//@ ensures unfolding l.Mem(elems setminus set[*Element] { e }, true) in l.lenT == old(unfolding l.Mem(elems, true) in l.lenT) - 1
//@ ensures acc(e) && e.list == nil
//@ decreases  
func (l *List) remove(e *Element) () {
  //@ unfold l.Mem(elems, true)
  e.prev.next = e.next
  e.next.prev = e.prev
  e.next = nil
  e.prev = nil
  e.list = nil
  l.lenT -= 1
  //@ fold l.Mem(elems setminus set[*Element] { e }, true)
}

//@ ghost-parameters: elems set[*Element]
//@ requires l.Mem(elems, true)
//@ requires e in elems
//@ requires at in elems
//@ ensures l.Mem(elems, true)
//@ ensures e != at ==> unfolding l.Mem(elems, true) in at.next == e && e.prev == at
//@ decreases  
func (l *List) move(e *Element, at *Element) () {
  if e == at {
    
  }
  //@ unfold l.Mem(elems, true)
  e.prev.next = e.next
  e.next.prev = e.prev
  e.prev = at
  e.next = at.next
  e.prev.next = e
  e.next.prev = e
  //@ fold l.Mem(elems, true)
}

//@ ghost-parameters: elems set[*Element]
//@ requires e != nil
//@ requires l.Mem(elems, true)
//@ requires e != (&l.root)
//@ requires !e in elems ==> elems == elems setminus set[*Element] { e }
//@ requires !e in elems ==> acc(e) && e.list != l
//@ requires e in elems ==> unfolding l.Mem(elems, true) in e.list == l
//@ requires unfolding l.Mem(elems, true) in (e.list == l ==> e in elems) && (e.list != l ==> !e in elems)
//@ ensures !e in elems ==> l.Mem(elems, true)
//@ ensures e in elems ==> l.Mem(elems setminus set[*Element] { e }, true) && !e in elems setminus set[*Element] { e }
//@ ensures acc(e) && e.Value === res && (e in elems ==> e.list == nil)
//@ decreases  
func (l *List) Remove(e *Element) (res any) {
  /*@
   ghost if e in elems {
    unfold l.Mem(elems, true)
  }
  @*/
  if e.list == l {
    //@ fold l.Mem(elems, true)
    l.remove(e) /*@ with: elems @*/
  }
  return e.Value
}

//@ ghost-parameters: elems set[*Element], isInit bool
//@ requires l.Mem(elems, isInit)
//@ ensures l.Mem(elems union set[*Element] { res }, true)
//@ ensures isInit ==> unfolding l.Mem(elems union set[*Element] { res }, true) in l.lenT == 1 + old(unfolding l.Mem(elems, true) in l.lenT)
//@ ensures !isInit ==> unfolding l.Mem(elems union set[*Element] { res }, true) in l.lenT == 1
//@ ensures unfolding l.Mem(elems union set[*Element] { res }, true) in l.root.next == res && res.prev == (&l.root)
//@ decreases  
func (l *List) PushFront(v any) (res *Element) {
  l.lazyInit() /*@ with: elems, isInit @*/
  res = l.insertValue(v, &l.root) /*@ with: elems @*/
}

//@ ghost-parameters: elems set[*Element], isInit bool
//@ requires l.Mem(elems, isInit)
//@ ensures l.Mem(elems union set[*Element] { res }, true)
//@ ensures isInit ==> unfolding l.Mem(elems union set[*Element] { res }, true) in l.lenT == 1 + old(unfolding l.Mem(elems, true) in l.lenT)
//@ ensures !isInit ==> unfolding l.Mem(elems union set[*Element] { res }, true) in l.lenT == 1
//@ ensures unfolding l.Mem(elems union set[*Element] { res }, true) in res.next == (&l.root) && l.root.prev == res
//@ decreases  
func (l *List) PushBack(v any) (res *Element) {
  l.lazyInit() /*@ with: elems, isInit @*/
  //@ unfold l.Mem(elems, true)
  back := l.root.prev 
  //@ fold l.Mem(elems, true)
  return l.insertValue(v, back) /*@ with: elems @*/
}

//@ ghost-parameters: elems set[*Element]
//@ requires mark != nil
//@ requires l.Mem(elems, true)
//@ requires !mark in elems ==> acc(mark) && mark.list != l
//@ requires mark in elems ==> unfolding l.Mem(elems, true) in mark.list == l
//@ requires unfolding l.Mem(elems, true) in (mark.list == l ==> mark in elems) && (mark.list != l ==> !mark in elems)
//@ ensures mark in elems ==> l.Mem(elems union set[*Element] { res }, true)
//@ ensures !mark in elems ==> l.Mem(elems, true)
//@ ensures mark in elems ==> unfolding l.Mem(elems union set[*Element] { res }, true) in mark.prev == res && res.next == mark
//@ decreases  
func (l *List) InsertBefore(v any, mark *Element) (res *Element) {
  //@ unfold l.Mem(elems, true)
  if mark.list != l {
    //@ fold l.Mem(elems, true)
    return nil
  }
  markPrev := mark.prev 
  //@ fold l.Mem(elems, true)
  return l.insertValue(v, markPrev) /*@ with: elems @*/
}

//@ ghost-parameters: elems set[*Element]
//@ requires mark != nil
//@ requires l.Mem(elems, true)
//@ requires !mark in elems ==> acc(mark) && mark.list != l
//@ requires mark in elems ==> unfolding l.Mem(elems, true) in mark.list == l
//@ requires unfolding l.Mem(elems, true) in (mark.list == l ==> mark in elems) && (mark.list != l ==> !mark in elems)
//@ ensures mark in elems ==> l.Mem(elems union set[*Element] { res }, true)
//@ ensures !mark in elems ==> l.Mem(elems, true)
//@ ensures mark in elems ==> unfolding l.Mem(elems union set[*Element] { res }, true) in mark.next == res && res.prev == mark
//@ decreases  
func (l *List) InsertAfter(v any, mark *Element) (res *Element) {
  //@ unfold l.Mem(elems, true)
  if mark.list != l {
    //@ fold l.Mem(elems, true)
    return nil
  }
  //@ fold l.Mem(elems, true)
  return l.insertValue(v, mark) /*@ with: elems @*/
}

//@ ghost-parameters: elems set[*Element]
//@ requires e != nil
//@ requires e != (&l.root)
//@ requires l.Mem(elems, true)
//@ requires !e in elems ==> acc(e) && e.list != l
//@ requires e in elems ==> unfolding l.Mem(elems, true) in e.list == l
//@ requires unfolding l.Mem(elems, true) in (e.list == l ==> e in elems) && (e.list != l ==> !e in elems)
//@ ensures l.Mem(elems, true)
//@ ensures e in elems ==> unfolding l.Mem(elems, true) in l.root.next == e && e.prev == (&l.root)
//@ decreases  
func (l *List) MoveToFront(e *Element) () {
  //@ unfold l.Mem(elems, true)
  if e.list != l || l.root.next == e {
    //@ fold l.Mem(elems, true)
    
  }
  //@ fold l.Mem(elems, true)
  l.move(e, &l.root) /*@ with: elems @*/
}

//@ ghost-parameters: elems set[*Element]
//@ requires e != nil
//@ requires l.Mem(elems, true)
//@ requires !e in elems ==> acc(e) && e.list != l
//@ requires e in elems ==> unfolding l.Mem(elems, true) in e.list == l
//@ requires unfolding l.Mem(elems, true) in (e.list == l ==> e in elems) && (e.list != l ==> !e in elems)
//@ ensures l.Mem(elems, true)
//@ decreases  
func (l *List) MoveToBack(e *Element) () {
  //@ unfold l.Mem(elems, true)
  if e.list != l || l.root.prev == e {
    //@ fold l.Mem(elems, true)
    
  }
  back := l.root.prev 
  //@ fold l.Mem(elems, true)
  l.move(e, back) /*@ with: elems @*/
}

//@ ghost-parameters: elems set[*Element]
//@ requires e != nil
//@ requires mark != nil
//@ requires l.Mem(elems, true)
//@ requires !e in elems ==> acc(e) && e.list != l
//@ requires e in elems ==> unfolding l.Mem(elems, true) in e.list == l
//@ requires unfolding l.Mem(elems, true) in (e.list == l ==> e in elems) && (e.list != l ==> !e in elems)
//@ requires !mark in elems ==> acc(mark) && mark.list != l
//@ requires mark in elems ==> unfolding l.Mem(elems, true) in mark.list == l
//@ requires unfolding l.Mem(elems, true) in (mark.list == l ==> mark in elems) && (mark.list != l ==> !mark in elems)
//@ ensures l.Mem(elems, true)
//@ decreases  
func (l *List) MoveBefore(e *Element, mark *Element) () {
  //@ unfold l.Mem(elems, true)
  if e.list != l || e == mark || mark.list != l {
    //@ fold l.Mem(elems, true)
    
  }
  markPrev := mark.prev 
  //@ fold l.Mem(elems, true)
  l.move(e, markPrev) /*@ with: elems @*/
}

//@ ghost-parameters: elems set[*Element]
//@ requires e != nil
//@ requires mark != nil
//@ requires l.Mem(elems, true)
//@ requires !e in elems ==> acc(e) && e.list != l
//@ requires e in elems ==> unfolding l.Mem(elems, true) in e.list == l
//@ requires unfolding l.Mem(elems, true) in (e.list == l ==> e in elems) && (e.list != l ==> !e in elems)
//@ requires !mark in elems ==> acc(mark) && mark.list != l
//@ requires mark in elems ==> unfolding l.Mem(elems, true) in mark.list == l
//@ requires unfolding l.Mem(elems, true) in (mark.list == l ==> mark in elems) && (mark.list != l ==> !mark in elems)
//@ ensures l.Mem(elems, true)
//@ ensures mark != e && e in elems && mark in elems ==> unfolding l.Mem(elems, true) in mark.next == e && e.prev == mark
//@ decreases  
func (l *List) MoveAfter(e *Element, mark *Element) () {
  //@ unfold l.Mem(elems, true)
  if e.list != l || e == mark || mark.list != l {
    //@ fold l.Mem(elems, true)
    
  }
  //@ fold l.Mem(elems, true)
  l.move(e, mark) /*@ with: elems @*/
}

//@ ghost-parameters: elemsL set[*Element], elemsOther set[*Element], isInit bool
//@ requires false
func (l *List) PushBackList(other *List) () {
  l.lazyInit() /*@ with: elemsL, isInit @*/
  for i, e := other.Len() /*@ with: elemsOther @*/, other.Front() /*@ with: elemsOther @*/ ; i > 0; i, e = i - 1, e.Next() /*@ with: elemsOther, other @*/ {
    l.insertValue(e.Value, l.root.prev) /*@ with: elemsL @*/
  }
}

//@ ghost-parameters: elemsL set[*Element], elemsOther set[*Element], isInit bool
//@ requires false
//@ requires l.Mem(elemsL, isInit)
//@ requires l == other ==> elemsL == elemsOther
//@ requires l != other ==> other.Mem(elemsOther, true)
func (l *List) PushFrontList(other *List) () {
  l.lazyInit() /*@ with: elemsL, isInit @*/
  //@ assert l.Mem(elemsL, true)
  for i, e := other.Len() /*@ with: elemsOther @*/, other.Back() /*@ with: elemsOther @*/ ; i > 0; i, e = i - 1, e.Prev() /*@ with: elemsOther, other @*/ {
    //@ unfold other.Mem(elemsOther, true)
    eValue := e.Value 
    //@ fold other.Mem(elemsOther, true)
    newElem := l.insertValue(eValue, &l.root) /*@ with: elemsL @*/ 
  }
}

type Element struct {
  next, prev *Element
  list *List
  Value any
} 

type List struct {
  root Element
  lenT int
} 

/*@
pred (l *List) Mem(ghost s set[*Element], ghost isInit bool) {
  acc(&l.lenT) && &l.root in s && forall i: *Element ::  i in s ==> acc(&i.next) && acc(&i.prev) && acc(&i.list) && acc(&i.Value) && (l.root.next == nil || l.root.prev == nil ==> !isInit) && (!isInit ==> len(s) == 1 && s == set[*Element] { &l.root } && l.root.next == nil && l.root.prev == nil) && (isInit ==> len(s) >= 1 && l.lenT == len(s) - 1 && forall i: *Element ::  i in s ==> i.next != nil && i.prev != nil && (i != (&l.root) ==> i.list == l) && forall i: *Element, j: *Element ::  i in s && i.next == j ==> j in s && j.prev == i && i.next.prev == i && j.prev.next == j && forall i: *Element, j: *Element ::  i in s && i.prev == j ==> j in s && j.next == i && i.prev.next == i && j.next.prev == j)
}
@*/

