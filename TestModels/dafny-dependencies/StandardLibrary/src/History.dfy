
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
    {
      events := events + [e];
    }

    function NthLastEvent(n: nat): Event
      requires n < |events|
      reads this
    {
      events[|events| - 1 - n]
    }

    function LastEvent(): Event
      requires 0 < |events|
      reads this
    {
      NthLastEvent(0)
    }
  }
}