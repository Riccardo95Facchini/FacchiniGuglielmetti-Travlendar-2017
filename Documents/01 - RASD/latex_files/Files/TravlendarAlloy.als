//Dates are calculated as the number of seconds from the 
//1st January 1970 following the UNIX standard

//--------------------------------------SIGNATURES-------------------------------------
open util/boolean

//The GPS position is represented as two integers for semplicity
sig GPSLocation{
	latitude: one Int,
	longitude: one Int
}

//A single event recorded inside the user's calendar
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

//The flexible break the user can set during the day
sig Break{
	start : one Int,
	end: one Int,
	duration: one Int
}{
	start < end  and
	minus[end, start] > duration and
	duration > 0
}

//The calendar of a user, containing all the events.
sig Calendar{
	events: set Event
}{
	no disj e1, e2 : Event | !noOverlap[e1, e2]
}

//A model of the user
sig User{
	email: one Int,
	gpsLocation : one GPSLocation,
	preferences: one Preference,
	compiles: one Calendar
}

//The preferences specified by the user (A.K.A. options/settings)
sig Preference{
	preferedVehicle : set Vehicle,
	ownedVehicle : set Vehicle,
	breaks : set Break
}{
	no disj v1, v2 : Vehicle | v1 in preferedVehicle and 
	v2 in preferedVehicle and  v1 in ownedVehicle and 
	v2 in ownedVehicle 
}

//The weather forecast for a trip, we consider it accurate all the time
sig Weather{
	rain : Bool
}

//The trip itself from point A to point B
sig Trip{
	duration : one Int, 
	vehicles : some Vehicle
}{
	all t : Trip | some e : Event | t in e.trip
}
//---------------------------ABSTRACT SIGNATURES-------------------------------

//A vehicle/means of transport, either owned, public transport or shared.
abstract sig Vehicle{
	type : one Int
}

//For semplicity "Foot" is modeled as a vehicle
sig Foot extends Vehicle{}
sig Bicycle extends Vehicle {}
sig Car extends Vehicle {}
sig Bus extends Vehicle {}
sig Tram extends Vehicle {}
sig Train extends Vehicle {}

//Public transportation unavailability
abstract sig Strike{
	startingTime: one Int, 
	endingTime: one Int,
	area: some GPSLocation	
}

sig BusStrike extends Strike{} 
sig TramStrike extends Strike{} 
sig TrainStrike extends Strike{} 

//--------------------------------------FACTS-------------------------------------

//No two users have the same email
fact allUniqueUsers{
	no disj u1, u2 : User | u1.email = u2.email
}

//A calendar belongs to only one user
fact userHasOneCalendar{
	no disj u1, u2 : User | some c : Calendar |
		c in u1.compiles and c in u2.compiles
}

//A calendar cannot exists without its user
fact noUserNoCalendar{
	all c : Calendar | some u : User |
		c in u.compiles
}

//An event cannot exists without being in a calendar
fact noCalendarNoEvent{
	all e : Event | some c : Calendar |
		e in c.events
}

//A preference cannot exists without a user that chose it
fact noUserNoPreferences{
	all p : Preference | some u : User |
		p in u.preferences
}

//Given the interval of a break it must be assured that at 
//least the specified duration is free, in other words there 
//always is an amount of free time equals to the break 
//duration during a break interval.
fact MinimumBreakDuration{
	all e1, e2 : Event, b : Break |
	e1. endingTime < e2.startingTime and e1.endingTime > b.start 
	and e2.startingTime < b.end
	implies minus[e2.startingTime, e1.endingTime] >= b.duration
}

//When it rains the trip must not contain a bike as transportation mean
fact noBicycleWhenRains{
	all e : Event | e.weather.rain = True implies 
	(no b: Bicycle | b in e.trip.vehicles)
}

//During a bus strike the trip must not contain a bus as transportation mean
fact noBusWhenStriked{
	all e: Event | some bs : BusStrike | eventDuringStrike[e, bs] implies 
		(no b : Bus | b in e.trip.vehicles)
}

//During a tram strike the trip must not contain a tram as transportation mean
fact noTramWhenStriked{
	all e: Event | some ts : TramStrike | eventDuringStrike[e, ts] implies 
		(no t : Tram | t in e.trip.vehicles)
}

//During a train strike the trip must not contain a train as transportation mean
fact noTrainWhenStriked{
	all e: Event | some ts : TrainStrike | eventDuringStrike[e, ts] implies 
		(no t : Train | t in e.trip.vehicles)
}

//Breaks must not overlap with one another
fact noBreakOverlap{
	all disj b1, b2 : Break |
		b1.start < b2.start and b1.end < b2.start or 
		b2.start < b1.start and b2.end < b1.start
}

//--------------------------------------PREDICATES-------------------------------------

//Addition of an event to a calendar
pred addEvent[c, c' : Calendar, e : Event]{
	c'.events = c.events + e
}

//Removal of an event from a calendar
pred deleteEvent[c, c': Calendar, e : Event]{
	c'.events = c.events - e
}

//Checking if an event is happening during a public transportation strike
pred eventDuringStrike[e : Event, s : Strike]{
	userStartingTime[e] > s.startingTime and 
	userStartingTime[e] < s.endingTime	
}

//Checking that events do not overlap with each other
pred noOverlap[e1, e2: Event]{
	e1.startingTime < e2.startingTime and 
	e1.endingTime < e2.startingTime or 
	e2.startingTime < e1.startingTime and 
	e2.endingTime < e1.startingTime
}

//Shows the addEvent predicate
pred showAdd[c, c' : Calendar, e : Event]{
	addEvent[c, c', e]
	#Calendar.events > 2
}

//Shows the deleteEvent predicate
pred showDelete[c, c' : Calendar, e : Event]{
	deleteEvent[c, c', e]
	#Calendar.events > 1
}

//--------------------------------------FUCNTIONS-------------------------------------

//When the user has to leave in order to reach the meeting in time
fun userStartingTime[e : Event] : Int{
	minus[e.startingTime, e.trip.duration]
}

//--------------------------------------ASSERTIONS-------------------------------------

//Assertion to prove that no event overlap with another
assert noOverlappingEvents{
	all c, c': Calendar|
		all e1, e2, e3: Event | e1 in c.events and e2 in c.events  
		and !(e3 in c.events) 
		and !noOverlap[e1, e2] and addEvent[c, c', e3]
		implies !noOverlap[e1, e3] and !noOverlap[e2, e3]
}check noOverlappingEvents for 6 but 1 Calendar

//Assertion to prove that during the span of a break there is time for the pause
assert minimumDurationGuaranteed{
	all c, c':Calendar, e : Event, p : Preference |
		addEvent[c, c', e] implies 
			(all e1 : Event, b : Break | 
				e1 in c'.events  and b in p.breaks and 
				e.endingTime < e1.startingTime and 
				e.endingTime > b.start and 
				e1.startingTime < b.end implies 
				minus[e1.startingTime, e.endingTime] >= b.duration)
}
check minimumDurationGuaranteed for 6

//Assertion to prove that a trip as at least one vehicle, makin it valid
assert validTrip{
	all e : Event |  #e.trip.vehicles > 0
}
check validTrip for 6

//Assertion to prove that during a strike of a vehicle that vehicle will not be 
//inside the chosen ones
assert noStrikedVehiclesInTrip{
	all e : Event | some bs : BusStrike,  ts : TramStrike, trs : TrainStrike | 
	(eventDuringStrike[e, bs] implies (no b : Bus | b in e.trip.vehicles) and 
		eventDuringStrike[e, ts] implies (no t : Tram | t in e.trip.vehicles) and
		eventDuringStrike[e, trs] implies (no t : Train | t in e.trip.vehicles))
}
check noStrikedVehiclesInTrip for 6

pred show{}

run show for 5 but exactly 1 User, 3 Event, 2 Break
