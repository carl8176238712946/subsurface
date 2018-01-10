open util/ordering[State]

sig Data {}
sig Subsystem {}
sig Channel {}

sig State {
  transmission_state_b: set Subsystem lone -> lone Data,
  receive_state_b: set Subsystem lone -> lone Data,

  generation_state_b: set Data lone -> lone Subsystem,
  generation_state_c: set Data -> lone Subsystem,
  
  data_receive_state_b: set Data lone -> set Subsystem,
  data_receive_state_c: set Data -> set Subsystem,
  
  connected: set Channel -> set Subsystem,
  carried_by: set Data -> lone Channel,

  compromised: set Subsystem,
  can_authorise: set Subsystem,
  malicious: set Data,
  authorised: set Data,

  accepted: set Subsystem -> set Data,

  secure:set Channel,

  identity_of: set Subsystem -> one Subsystem,

  officially_recognised: set Subsystem

} {
  //- each data object can only be one generation state
  no ~generation_state_b.generation_state_c

  //- subsystems can't transmit and receive data simultaneously
  no ~receive_state_b.transmission_state_b

  //- subsystem transitioning to transmission_b
  //- must be simultaneous with data moving to generation_b
  ~transmission_state_b = generation_state_b
  ~receive_state_b = data_receive_state_b

  //- data in receive state must be in generate state c
  data_receive_state_b.Subsystem in generation_state_c.Subsystem
  data_receive_state_c.Subsystem in generation_state_c.Subsystem

  //- can't receive data twice
  no data_receive_state_c & data_receive_state_b

  //- subsystem can't receive it's own generated data
  no generation_state_c & data_receive_state_b
  no generation_state_c & data_receive_state_c

  //- generated data must be carried by a channel 
  generation_state_b.~connected in carried_by
  carried_by.Channel = (generation_state_b + generation_state_c).Subsystem

  //- all transmitting subsystems must connect to a channel
  transmission_state_b.Data in Channel.connected 

  //- all receiving subsystems must connect to the data-carrying channel
  receive_state_b.carried_by in ~connected

  //- uncompromised subsystems always have their own identity
  Subsystem.(identity_of & iden) = (Subsystem - compromised)

}

fact {

   //- CASE 1: no mitigation, all subsystems accept received data
   //all s:State | s.accepted = ~(s.data_receive_state_c)

   //- CASE 2a: compromised subsystems cannot accept data from secure channel
   all s:State | s.accepted in ~(s.data_receive_state_c)
 
   all s:State, s':s.next, x:Subsystem, d:Data |
            receive_end[s',x,d]
      && (x in s'.compromised)
      && (d.(s'.carried_by) in s'.secure)
      =>
      !((x->d) in s'.accepted)

   //- CASE 2b: subsystems will not accept unauthorised data
   all s:State, s':s.next, x:Subsystem, d:Data |
            receive_end[s',x,d]
      && !(d in s'.authorised)
      =>
      !((x->d) in s'.accepted)   

   //- CASE 2c: uncompromised subsystems only receive data from
   //- officially recognised subsystems
   all s:State, s':s.next, x:Subsystem, d:Data |
            receive_end[s',x,d]
      && !(x in s'.compromised)
      && !(d.(s'.generation_state_c) in s'.officially_recognised)
      =>
      !((x->d) in s'.accepted)   

  


    //- the channel that carries data does not change
    //all s:State, s':s.next | s.carried_by in s'.carried_by 

    //- subsystems that accept data cannot later discard it
    all s:State, s':s.next, x:Subsystem, d:Data |
      !receive_end[s',x,d] => (((x->d) in s.accepted) <=> ((x->d) in s'.accepted))


    //- data is either malicious or not (cannot change)
    all s:State, s':s.next | s.malicious = s'.malicious

    //- data is either authorised or not (cannot change)
    all s:State, s':s.next | s.authorised = s'.authorised 

    //- subsystems are either recognised or not (cannot change)
    all s:State, s':s.next | s.officially_recognised = s'.officially_recognised

  //- subsystems that receive malicious data become compromised
  all s:State, s':s.next, x:Subsystem, d:Data |
    receive_end[s',x,d]  && d in s.malicious && (x->d) in s'.accepted => x in s'.compromised

  //- only compromised subsystems generate malicious data
  all s:State, s':s.next, x:Subsystem, d:Data |
    transmission_start[s',x,d]  && d in s.malicious => x in s'.compromised

  //- only can_authorise subsystems generate authorised data
  all s:State, s':s.next, x:Subsystem, d:Data |
    transmission_start[s',x,d] && d in s.authorised => x in s'.can_authorise
  
  //- data in generate state c must have been in state b or c
  all s:State, s':s.next, d:Data |
        //- from b: stay in state b or go to state c
        d.(s.generation_state_b) in (d.(s'.generation_state_b) + d.(s'.generation_state_c))
        //- state c must come from b or c
   && d.(s'.generation_state_c) in (d.(s.generation_state_b) + d.(s.generation_state_c))
        //- from c: stay in state c
   && d.(s.generation_state_c) in d.(s'.generation_state_c)


  //- data in receive state c must have been in state b or c
  all s:State, s':s.next, x:Subsystem |
        //- from b: stay in state b or go to state c
        (s.data_receive_state_b).x in ((s'.data_receive_state_b).x + (s'.data_receive_state_c).x)
        //- state c must come from b or c
   && (s'.data_receive_state_c).x in ((s.data_receive_state_b).x + (s.data_receive_state_c).x)
        //- from c: stay in state c
   && (s.data_receive_state_c).x in (s'.data_receive_state_c).x


   
  //- during transmission subsystems either continue transmission or finish
  //- (cannot immediately start transmitting new data)
  all s:State, s':s.next, x:Subsystem |
    (no x.(s.transmission_state_b)) ||
    (x.(s'.transmission_state_b) in x.(s.transmission_state_b))



}

pred receive_end[s':State, x:Subsystem, d:Data] {
  some s:s'.prev |
           (x->d) in s.receive_state_b 
    && !((x->d) in s'.receive_state_b)
}

pred transmission_start[s':State, x:Subsystem, d:Data] {
  some s:s'.prev |
           (x->d) in s'.transmission_state_b 
    && !((x->d) in s.transmission_state_b)
}

run {
  //- data moving through generation states
  some s1:State, s2:s1.next |
    some d:Data | some sub:Subsystem|
      (d->sub) in s1.generation_state_b &&  
      (d->sub) in s2.generation_state_c
} for
exactly 2 State
, exactly 1 Subsystem
, exactly 1 Data
, exactly 1 Channel

run {} for
exactly 3 State
, exactly 1 Subsystem
, exactly 1 Data
, exactly 1 Channel


//- scenario test: receiving malicious data
run {
  //- scenario with malicious data
  some d:Data | d in State.malicious

  //- subsystems are always connected to the (only) channel
  all s:State | all x:Subsystem | some c: Channel | (c->x) in s.connected

  //- subsystem rececives data, and was not compromised before that
  some s:State, x:Subsystem, d:Data |
    receive_end[s,x,d] && no (s.^prev).compromised

} for
exactly 2 State
, exactly 2 Subsystem
, exactly 1 Data
, exactly 1 Channel


//- scenario test: generating malicious data
run {
  //- scenario with malicious data
  some d:Data | d in State.malicious

  //- subsystems are always connected to the (only) channel
  all s:State | all x:Subsystem | some c: Channel | (c->x) in s.connected

  //- subsystem rececives data, and was not compromised before that
  some s:State, x:Subsystem, d:Data |
    transmission_start[s,x,d]

    //- this condition should fail (no instances found)
    //&& !(x in s.compromised)

} for
exactly 3 State
, exactly 1 Subsystem
, exactly 1 Data
, exactly 1 Channel




//- scenario test: subsystem holding on to generated data before sending
run {
  no State.malicious
  no State.compromised
    //- subsystems are always connected to the (only) channel
  all s:State | all x:Subsystem | some c: Channel | (c->x) in s.connected


} for
exactly 3 State
, exactly 1 Subsystem
, exactly 1 Data
, exactly 1 Channel



//- scenario test: subsystem holding on to generated data before sending
run {
  no State.malicious
  no State.compromised
  no State.secure
    //- subsystems are always connected to the (only) channel
  all s:State | all x:Subsystem | some c: Channel | (c->x) in s.connected

  some s:first.next, x:Subsystem, d:Data | receive_end[s,x,d]


} for
exactly 4 State
, exactly 2 Subsystem
, exactly 1 Data
, exactly 1 Channel



//- scenario test (should be UNSAT): can data stop being carried by a channel?
run {
  no State.malicious
  no State.compromised
  no State.secure
    //- subsystems are always connected to the (only) channel
  all s:State | all x:Subsystem | some c: Channel | (c->x) in s.connected

  some s:State, s':s.^next, d:Data, c:Channel |
    (d->c) in (s.carried_by) && !((d->c) in (s'.carried_by))


} for
exactly 4 State
, exactly 1 Subsystem
, exactly 1 Data
, exactly 1 Channel


//- scenario test: eaves dropping
run {
  no State.malicious
 
   //- subsystems are always connected to the (only) channel
  all s:State | all x:Subsystem | some c: Channel | (c->x) in s.connected

  //- data is initial uncreated
  no first.carried_by

  //- only one compromised subsystem
  some disj x,y,z:Subsystem | all s:State |
         x in s.compromised
    && !(y in s.compromised)
    && !(z in s.compromised)

  //- data generated by non-compromised subsystem
  all s:State, x:Subsystem, d:Data |
    ((x->d) in s.transmission_state_b) => !(x in s.compromised)

  //- in some state compromised subsystem accepts data
  some s:State, x:Subsystem, d:Data |
    x in s.compromised && (x->d) in s.accepted

  //- options:
  //no State.secure //- unsecure channel
  all s:State, c:Channel | c in s.secure //- secure channel

} for
exactly 4 State
, exactly 3 Subsystem
, exactly 1 Data
, exactly 1 Channel



//- scenario test: subsystems discard unauthorised data
run {
  no State.malicious
  no State.secure
  no State.compromised

   //- subsystems are always connected to the (only) channel
  all s:State | all x:Subsystem | some c: Channel | (c->x) in s.connected

  //- data is initial uncreated
  no first.carried_by

  //- only one subsystem can authorise
  some disj x,y:Subsystem | all s:State |
    x in s.can_authorise && !(y in s.can_authorise)

  //- in some state subsystem receives data
  some s:State, x:Subsystem, d:Data | receive_end[s,x,d] 

} for
exactly 4 State
, exactly 2 Subsystem
, exactly 1 Data
, exactly 1 Channel


//- scenario test: identify faking
//- authorisation to prevent accepting malicious data
//- if a compromised system cannot authorise data, can
//- a subsystem ever accept malicious data?
run {
 //- mitigation strategy (uncomment)
 //all s:State, x:Subsystem | x in s.can_authorise => !(x in s.compromised)

  //- data is initial uncreated
  no first.carried_by

  //- data is generated by unrecognised subsystem
  some s:State, d:Data | !(d.(s.generation_state_c) in s.officially_recognised)

  //- goal state: will pfficially recognised subsystem x accepts malicious data
  some s:State, x:Subsystem, d:Data |
    x in s.officially_recognised &&
    d in s.malicious && (x->d) in s.accepted
 
} for
exactly 4 State
, exactly 3 Subsystem
, exactly 1 Data
, exactly 1 Channel


//- test: uncompromised subsystem identity
run {
  no State.compromised
  no State.can_authorise
} for
exactly 2 State
, exactly 3 Subsystem
, exactly 0 Data
, exactly 0 Channel

//- test: officially recognised subsystems
run {
  no State.compromised
  no State.secure
  no State.malicious

   //- all subsystems can authorise
  all s:State | s.can_authorise = Subsystem

   //- subsystems are always connected to the (only) channel
  all s:State | all x:Subsystem | some c: Channel | (c->x) in s.connected

  //- data is initial uncreated
  no first.carried_by

  //- subsystem rececives data, and was not compromised before that
  some s:State, x:Subsystem, d:Data | receive_end[s,x,d]

} for
exactly 4 State
, exactly 2 Subsystem
, exactly 1 Data
, exactly 1 Channel

//- note: addition mitigation condition: discard data that
//- has your own identity (something suspicious clear is happening...)
