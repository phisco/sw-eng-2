open util/boolean

sig Car {
	coordinate: one Coordinate,
	battery: one Int,
	inUse: one Bool,
	reserved: one Bool,
	user: lone User
} {
	battery >= 0
	battery <= 100
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

fact OneUserPerEmail {
	all u1, u2: User | u1!=u2 => u1.email != u2.email
}

pred show {}

assert BijectionBetweenUserAndEmail {
	all u1, u2: User | u1=u2 <=> u1.email = u2.email
}

run show for 1 Coordinate, 2 Car, 2 Email, 2 User, 1 Int
check BijectionBetweenUserAndEmail
