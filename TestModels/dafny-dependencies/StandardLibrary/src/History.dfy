
module Histories {
  trait {:termination false} Event {
  }

  class History {
    ghost var events: seq<Event>

    ghost constructor() 
      ensures events == []
    {
      this.events := [];
    }

    ghost method AddEvent(e: Event) 
      modifies this
      ensures events == old(events) + [e]
      // ensures forall p: Event -> bool | p(e) :: NewEventSuchThat(p)
    {
      events := events + [e];
    }

    twostate predicate NewEventSuchThat(p: Event -> bool) 
      reads this 
    {
      && |events| == |old(events)| + 1
      && events[..(|events| - 1)] == old(events)
      && p(events[|events| - 1])
    }
  }
}