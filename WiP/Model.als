open util/boolean

sig Email {}

sig Password {}

sig Municipality {
	agents: set Authority
} {
	#agents > 0
}

sig Id {}

sig LicensePlate {}

sig Street {}

sig Position {}

abstract sig ViolationType {}
-- showing all subclasses is not the purpose of this model

abstract sig Notification {}

sig AvailableNotification extends Notification {
	report: one Report
}

sig EvaluatedNotification extends Notification {
	report: one Report,
	approved: Bool
}

sig Report {
	id: one Id,
	author: one User,
	municipality: one Municipality
}

abstract sig Customer {
	email: one Email,
	password: one Password
}

sig User extends Customer {
	-- the reports the user has sent
	reports: set Report,
	-- list of new evaluated reports
	notifications: set EvaluatedNotification
}

sig Authority extends Customer {
	-- the reports the authority has to evaluate
	reports: set Report,
	-- the working place of the authority
	municipalities: set Municipality,
	-- list of new available reports
	notifications: set AvailableNotification
} {
	#municipality > 0
}

-- every e-mail address must be associated to a user or an authority
fact {
	all mailaddr : Email | some c : Customer | mailaddr in c.email
}

-- just to simplify the alloy model
fact {
	no disj c1,c2: Customer | c1.password = c2.password
}

-- every password address must be associated to a user or an authority
fact {
	all pw : Password | some c : Customer | pw in c.password
}

-- every customer must have a unique e-mail address
fact {
	no disj c1,c2: Customer | c1.email = c2.email
}

-- each authority must work in at least one municipality
fact {
	all a : Authority | some m : Municipality | a in m.agents
}

-- each report must have a unique identification number
fact {
	no disj r1,r2: Report | r1.id = r2.id
}

-- every id belongs to a report
fact {
	all i : Id | some r : Report | i = r.id
}

-- every authority must receive all the reports in his working places
fact {
	all r : Report | all a : Authority | r.municipality in a.municipalities iff r in a.reports
}

-- every authority works in a municipality if and only if that municipality is in his working places
fact {
	all a : Authority, m : Municipality | a in m.agents iff m in a.municipalities
}

-- evey evaluated notification must belong to one user
fact {
	all en : EvaluatedNotification | one u : User | en in u.notifications
}

-- every report must produce not more than one evaluated notification
fact {
	all r : Report | lone en : EvaluatedNotification | en.report = r
}

-- every report must produce not more than one available notification
fact {
	all r : Report | lone an : AvailableNotification | an.report = r
}

-- every user can receive only notifications for his own reports
fact {
	all en : EvaluatedNotification | one u : User | en in u.notifications and en.report in u.reports
}

-- every authority must receive the available notifications for his working areas
fact {
	all an : AvailableNotification, a : Authority | 
		an.report.municipality in a.municipalities implies an in a.notifications
}

-- every report must notify the authorities of that municipality
fact {
	all r : Report, a : Authority, an : AvailableNotification | r.municipality in a.municipalities
		implies an in a.notifications and an.report = r
}

-- every evaluated notification must belong to the user that sent the report
fact {
	all en : EvaluatedNotification | some u : User | en.report in u.reports
}


pred show () {}

run show for 3






