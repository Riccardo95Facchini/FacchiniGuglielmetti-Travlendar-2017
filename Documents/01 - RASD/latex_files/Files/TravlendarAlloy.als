//todo aggiustare create appointment in base a lunch e aggiungere ending time appuntamento in R19
//a user can have all vehicles that is preferred but now owned
//create appointment, now starting time and starting location are departure ecc...

//Dates are calculated as the number of seconds from the 1st January 1970

//--------------------------------------SIGS-------------------------------------
open util/boolean

sig GPSLocation{
	latitude: one Int,
	longitude: one Int
}

sig Event{
	startingTime: one Int,
	endingTime: one Int,
	place: one GPSLocation,
	weather : one Weather,
	strike : set Strike,
	trip: one Trip
}{
	endingTime > startingTime
}

//break and event can derive from a super class?
sig Break{
	start : one Int,
	end: one Int,
	duration: one Int
}{
	start < end  and
	minus[end, start] > duration and
	duration > 0
}

sig Calendar{
	events: set Event
}{
	no disj e1, e2 : Event | !noOverlap[e1, e2]
}

sig User{
	email: one Int,
	gpsLocation : one GPSLocation,
	preferences: one Preference,
	compiles: one Calendar
}

sig Preference{
	preferedVehicle : set Vehicle,
	ownedVehicle : set Vehicle,
	breaks : set Break
}{
	no disj v1, v2 : Vehicle | v1 in preferedVehicle and v2 in preferedVehicle and 
	 v1 in ownedVehicle and v2 in ownedVehicle 
	//no disj b1, b2 : Break | !noOverlapBreak[b1, b2]
}

abstract sig Vehicle{
	type : one Int
}

sig Foot extends Vehicle{}
sig Bicycle extends Vehicle {}
sig Car extends Vehicle {}
sig Bus extends Vehicle {}
sig Tram extends Vehicle {}
sig Train extends Vehicle {}

abstract sig Strike{
	startingTime: one Int, 
	endingTime: one Int,
	area: some GPSLocation	
}

sig BusStrike extends Strike{} 
sig TramStrike extends Strike{} 
sig TrainStrike extends Strike{} 

sig Weather{
	rain : Bool
}

sig Trip{
	duration : one Int, 
	vehicles : some Vehicle
}{
	all t : Trip | some e : Event | t in e.trip
}

//_______________________FACTS_____________________________

//all users have different email
fact allUniqueUsers{
	no disj u1, u2 : User | u1.email = u2.email
}

//a calendar belongs to only one user
fact userHasOneCalendar{
	no disj u1, u2 : User | some c : Calendar |
		c in u1.compiles and c in u2.compiles
}

//a calendar cannot exists without a user
fact noUserNoCalendar{
	all c : Calendar | some u : User |
		c in u.compiles
}

//an event cannot exists without a calendar
fact noCalendarNoEvent{
	all e : Event | some c : Calendar |
		e in c.events
}

//a preference cannot exists without a user
fact noUserNoPreferences{
	all p : Preference | some u : User |
		p in u.preferences
}

//the minimum duration of a break must be assured
fact MinimumBreakDuration{
	all e1, e2 : Event, b : Break |
		e1. endingTime < e2.startingTime and e1.endingTime > b.start and e2.startingTime < b.end
		implies minus[e2.startingTime, e1.endingTime] >= b.duration
}

//all breaks must not overlap
fact noBreakOverlap{
	all disj b1, b2 : Break |
		b1.start < b2.start and b1.end < b2.start or 
		b2.start < b1.start and b2.end < b1.start
}

fact noBicycleWhenRains{
	all e : Event | e.weather.rain = True implies (no b: Bicycle | b in e.trip.vehicles)
}

fact noBusWhenStriked{
	all e: Event | some bs : BusStrike | eventDuringStrike[e, bs] implies 
		(no b : Bus | b in e.trip.vehicles)
}

fact noTramWhenStriked{
	all e: Event | some ts : TramStrike | eventDuringStrike[e, ts] implies 
		(no t : Tram | t in e.trip.vehicles)
}

fact noTrainWhenStriked{
	all e: Event | some ts : TrainStrike | eventDuringStrike[e, ts] implies 
		(no t : Train | t in e.trip.vehicles)
}

//_____________________PRED_______________________________________

pred addEvent[c, c' : Calendar, e : Event]{
	c'.events = c.events + e
}

pred deleteEvent[c, c': Calendar, e : Event]{
	c'.events = c.events - e
}

//pred modifyEvent[c, c': Calendar, eBefore, eAfter : Event]{
//	eBefore in c.events and !(eBefore in c'.events) and eAfter in c'.events and !(eAfter in c.events)
//}

pred eventDuringStrike[e : Event, s : Strike]{
	userStartingTime[e] > s.startingTime and 	userStartingTime[e] < s.endingTime	
}

pred noOverlap[e1, e2: Event]{
	e1.startingTime < e2.startingTime and e1.endingTime < e2.startingTime or 
		e2.startingTime < e1.startingTime and e2.endingTime < e1.startingTime
}

pred noOverlapBreak[b1, b2: Break]{
	b1.start < b2.start and b1.end < b2.start or 
		b2.start < b1.start and b2.end < b1.start
}

pred showAdd[c, c' : Calendar, e : Event]{
	addEvent[c, c', e]
	#Calendar.events > 2
}

pred showDelete[c, c' : Calendar, e : Event]{
	deleteEvent[c, c', e]
	#Calendar.events > 1
}

//____________________FUN___________________________

fun userStartingTime[e : Event] : Int{
	minus[e.startingTime, e.trip.duration]
}

//____________________ASSERT________________________

assert noOverlappingEvents{
	all c, c': Calendar|
		all e1, e2, e3: Event | e1 in c.events and e2 in c.events  and !(e3 in c.events) 
			and !noOverlap[e1, e2] and addEvent[c, c', e3]
			implies !noOverlap[e1, e3] and !noOverlap[e2, e3]
}check noOverlappingEvents for 6 but 1 Calendar


assert minimumDurationGuaranteed{
	all c, c':Calendar, e : Event, p : Preference |
		addEvent[c, c', e] implies 
			(all e1 : Event, b : Break | 
				e1 in c'.events  and b in p.breaks and e.endingTime < e1.startingTime and e.endingTime > b.start and 
				e1.startingTime < b.end implies minus[e1.startingTime, e.endingTime] >= b.duration)
}
check minimumDurationGuaranteed for 6

assert validTrip{
	all e : Event |  #e.trip.vehicles > 0
}
check validTrip for 6

assert noStrikedVehiclesInTrip{
	all e : Event | some bs : BusStrike,  ts : TramStrike, trs : TrainStrike | 
	(eventDuringStrike[e, bs] implies (no b : Bus | b in e.trip.vehicles) and 
		eventDuringStrike[e, ts] implies (no t : Tram | t in e.trip.vehicles) and
		eventDuringStrike[e, trs] implies (no t : Train | t in e.trip.vehicles))
}
check noStrikedVehiclesInTrip for 6

pred show{}

run show for 5 but exactly 1 User, 3 Event, 2 Break
