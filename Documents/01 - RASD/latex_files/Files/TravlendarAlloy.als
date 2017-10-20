//todo aggiustare create appointment in base a lunch e aggiungere ending time appuntamento in R19

//Dates are calculated as the number of seconds from the 1st January 1970

//--------------------------------------SIGS-------------------------------------

sig GPSLocation{
	latitude: one Int,
	longitude: one Int
}

sig Event{
	startingTime: one Int,
	endingTime: one Int,
	place: one GPSLocation,
}{
	endingTime > startingTime
}

//break and event can derive from a super class?
sig Breaks{
	start : one Int,
	end: one Int,
	duration: one Int
}{
	start < end  and
	minus[end, start] > duration and
	duration > 0
}

sig Calendar{
	events: set Event}{
	no disj e1, e2 : Event | !overlap[e1, e2]
}

sig User{
	email: one Int,
	gpsLocation : one GPSLocation,
	preferences: one Preference,
	compiles: one Calendar
}

sig Preference{
	preferedVehicle : set Vehicle,
}{
	no disj v1, v2 : Vehicle | v1 in preferedVehicle and v2 in preferedVehicle
}

sig Vehicle{name : one Int}


//-----------------------------FACTS-------------------------------------------

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

//----------------------------PREDS-----------------------------------------

pred overlap[e1, e2: Event]{
	e1.startingTime < e2.startingTime and e1.endingTime < e2.startingTime
}

pred show{}

run show
