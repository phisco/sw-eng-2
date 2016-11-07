open util/boolean

sig Car {
	coordinate: one Coordinate,
	battery: one Int,
	inUse: one Bool,
	reserved: one Bool,
	user: lone User
} {
	battery >= 0
	battery =< 100
}

sig Coordinate {}

sig User {
	email: one Email,
	carInUse: lone Car,
	carReserved: lone Car
}

fact SimmetryBetweenDriverAndCar1 {
	all u:User | #u.carReserved=1 => u.carReserved.user=u
	all u:User | #u.carInUse=1 => u.carInUse.user=u
	all c:Car | #c.user=1 and c.inUse.isTrue => c.user.carInUse=c
	all c:Car | #c.user=1 and c.reserved.isTrue => c.user.carReserved=c
}

fact InUseAndReservedSemantics {
	all c:Car | (#c.user=1 => (c.inUse.isTrue or c.reserved.isTrue))
		and (c.reserved.isTrue <=> #c.user.carReserved=1)
		and (c.inUse.isTrue <=> #c.user.carInUse=1)
}

fact ReservationAndUseAreMutuallyExclusive {
	all c:Car | (c.reserved.isTrue => c.inUse.isFalse) 
		and (c.inUse.isTrue => c.reserved.isFalse)
	all u:User | (#u.carInUse=1 => #u.carReserved=0) 
		and (#u.carReserved=1 => #u.carInUse=0)
}

sig Email {}

pred oneUserPerEmail {
	all u1, u2: User | u1!=u2 => u1.email != u2.email
}

sig PowerStation {
	capacity: one Int,
	coordinate: one Coordinate,
	carParked: set Car,
	numberParked: one Int
} {
	numberParked=#carParked
	numberParked=<capacity
	capacity>0
	all c:Car | c in carParked => c.inUse.isFalse
}

pred eachPowerStationIsInADifferentPlace {
	all p1, p2: PowerStation | p1!=p2 => p1.coordinate!=p2.coordinate
}

fact CarAtPowerStationHaveItsCoordinate {
	all c:Car, p:PowerStation | c in p.carParked => c.coordinate=p.coordinate
}

fact CarCanBePluggedToOnlyOneStationAtOnce {
	all c:Car | lone p:PowerStation | c in p.carParked
}

pred showStatic {
	eachPowerStationIsInADifferentPlace
	oneUserPerEmail
	all u1,u2:User | u1=u2 <=> u1.email=u2.email
}

pred reservedToInUse (c,c':Car, u,u':User) {
	c.reserved.isTrue
	c'.inUse.isTrue
	c.user=u
	c'.user=u'
	c.coordinate=c'.coordinate
	c.battery=c'.battery
	u.carReserved=c
	u'.carInUse=c'
	u.email=u'.email
	unplugCar[c]
}

pred unplugCar (c:Car) {
	all p:PowerStation | c in p.carParked => one p':PowerStation | (
		p'.carParked=p.carParked-c and
		p.capacity=p'.capacity and
		p.coordinate=p'.coordinate and    
		p.numberParked=plus[p'.numberParked,1]
	)
}

pred finishTripAndPlugIfPossible (c,c':Car) {
	c.inUse.isTrue
	c'.inUse.isFalse
	c'.reserved.isFalse
	c.coordinate=c'.coordinate
	c.battery=c'.battery
	plugCar[c']
}

pred plugCar (c':Car) {
	all p,p':PowerStation | p.capacity=p'.capacity and p.coordinate=p'.coordinate
	all p:PowerStation | p.coordinate=c'.coordinate and c' not in p.carParked => one p':PowerStation | (
		p'.carParked=p.carParked+c' and   
		p'.numberParked=plus[p.numberParked,1]
	)
}

pred reserveCar (c,c':Car, u,u':User) {
	#c.user=0
	c.inUse.isFalse
	c.reserved.isFalse
	#u.carReserved=0
	#u.carInUse=0
	c'.user=u'
	c'.reserved.isTrue
	c'.inUse.isFalse
	c.coordinate=c'.coordinate
	c.battery=c'.battery
	u'.carReserved=c'
	#u.carInUse=0
	u.email=u'.email
	powerStationEvolution[c,c']
	powerStationEvolution[c',c]
}

pred powerStationEvolution (c,c':Car) {
		all p:PowerStation | (c in p.carParked => (one p':PowerStation | (
		p'.carParked = p.carParked - c + c' and
		p.capacity=p'.capacity and
		p.coordinate=p'.coordinate and    
		p.numberParked=p'.numberParked )
	))
}

pred deleteReservation (c,c':Car, u,u':User) {
	reserveCar[c',c,u',u]
}

run showStatic for 2 Coordinate, 2 Car, 2 Email, 2 User, 2 Int, 1 PowerStation
run reservedToInUse for 1 Coordinate, 2 User, 2 Car, 1 Email, 2 PowerStation, 2 Int
run finishTripAndPlugIfPossible for 2 Coordinate, 1 User, 2 Car, 1 Email, 2 PowerStation, 2 Int
run reserveCar for 2 Coordinate, 2 User, 2 Email, 2 Car, 2 PowerStation, 2 Int
run deleteReservation for 2 Coordinate, 2 User, 2 Email, 2 Car, 2 PowerStation, 2 Int
