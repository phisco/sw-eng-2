open util/boolean

sig Car {
	coordinate: one Coordinate,
	battery: one Int,
	inUse: one Bool,
	user: lone User
} {
	battery >= 0
	battery <= 100
}

sig Coordinate {}

sig User {
	email: one Email,
	car: lone Car
}

fact SimmetryBetweenDriverAndCar1 {
	all u:User | #u.car=1 => u.car.user=u
}

fact SimmetryBetweenDriverAndCar2 {
	all c:Car | #c.user=1 => c.user.car=c
}

fact InUseSemantics {
	all c:Car | c.inUse.isTrue <=> #c.user=1
}

sig Email {}

fact OneUserPerEmail {
	all u1, u2: User | u1!=u2 => u1.email != u2.email
}

pred show {}

assert BijectionBetweenUserAndEmail {
	all u1, u2: User | u1=u2 <=> u1.email = u2.email
}

run show
check BijectionBetweenUserAndEmail
