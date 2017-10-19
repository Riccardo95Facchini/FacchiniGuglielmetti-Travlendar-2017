sig Date{}

sig GPSLocation{
	latitude: one Int,
	longitude: one Int
}

sig Event{
	date: one Date,
	place: one GPSLocation,
}

sig Calendar{
	events: set Event}{
	no disj e1, e2 : Event | 
		e1.place = e2.place or e1.date = e2.date
}

sig User{
	compiles: one Calendar}{
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

pred show{}

run show
