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
}

fact SimmetryBetweenDriverAndCar2 {
	all u:User | #u.carInUse=1 => u.carInUse.user=u
}

fact SimmetryBetweenDriverAndCar3 {
	all c:Car | #c.user=1 and c.inUse.isTrue => c.user.carInUse=c
}

fact SimmetryBetweenDriverAndCar4 {
	all c:Car | #c.user=1 and c.reserved.isTrue => c.user.carReserved=c
}

fact InUseAndReservedSemantics {
	all c:Car | (#c.user=1 => (c.inUse.isTrue or c.reserved.isTrue))
		and (c.reserved.isTrue <=> #c.user.carReserved=1)
		and (c.inUse.isTrue <=> #c.user.carInUse=1)
}

fact ReservationAndUseAreMutuallyExclusiveWrtCars {
	all c:Car | (c.reserved.isTrue => c.inUse.isFalse) 
		and (c.inUse.isTrue => c.reserved.isFalse)
}

fact ReservationAndUseAreMutuallyExclusiveWrtUsers {
	all u:User | (#u.carInUse=1 => #u.carReserved=0) 
		and (#u.carReserved=1 => #u.carInUse=0)
}

sig Email {}

fact OneUserPerEmail {//da fare solo nello statico
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

fact EachPowerStationIsInADifferentPlace {//da fare solo nello statico
	all p1, p2: PowerStation | p1!=p2 => p1.coordinate!=p2.coordinate
}

fact CarAtPowerStationHaveItsCoordinate {
	all c:Car, p:PowerStation | c in p.carParked => c.coordinate=p.coordinate
}

pred show {}

pred reservedToInUse (c,c':Car, u,u':User) {
	c.reserved.isTrue
	c'.inUse.isTrue
	c.user=u
	c'.user=u'
	c.coordinate=c'.coordinate
	c.battery=c'.battery
	u.carReserved=c
	u'.carInUse=c'
	//one p3:PowerStation | c in p3.carParked per trovare modello significativo
	//u.email=u'.email
	//da scommentare separando gli ambiti statico e dinamico
	unplugCar[c]
}

pred unplugCar (c:Car) {
	all p:PowerStation | c in p.carParked => one p2:PowerStation | (
		p2.carParked=p.carParked-c and
		p.capacity=p2.capacity and
		//p.coordinate=p'.coordinate and    
		//da scommentare separando gli ambiti statico e dinamico
		p.numberParked=plus[p2.numberParked,1]
	)
}

assert BijectionBetweenUserAndEmail {
	all u1,u2:User | u1=u2 <=> u1.email=u2.email
}

run show for 2 Coordinate, 2 Car, 2 Email, 2 User, 2 Int, 1 PowerStation
run reservedToInUse for 3 but 2 Int
check BijectionBetweenUserAndEmail
