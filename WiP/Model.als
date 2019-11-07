sig Email {}

sig Password {}

sig Municipality {}

sig

sig Report{
	municipality: one Municipality
}

abstract sig Customer {
	email: one Email,
	password: one Password
}

sig User extends Customer {
	-- the reports the user has sent
	reports: set Report
	-- if one of the user's reports has been just evaluated
	notified: one Bool
}

sig Authority extends Customer {
	-- the reports the authority has to evaluate
	reports: set Report
	-- if the authority has a new available report
	notified: one Bool
}

-- every customer must have a unique e-mail address
fact EmailIsUnique {
	no disj c1,c2: Customer | c1.email = c2.email
}


