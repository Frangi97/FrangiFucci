open util/boolean

sig Email {}

sig Password {}

sig Municipality {
	agents: set Authority
} {
	#agents > 0
}

sig Id {}

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
	-- the working place of the authority
	municipalities: set Municipality,
	-- list of new available reports
	notifications: set AvailableNotification
} {
	#municipalities > 0
}

-- every e-mail address must be associated to a user or an authority
fact {
	all mailaddr : Email | some c : Customer | mailaddr in c.email
}

-- just to simplify the alloy model
fact {
	no disj c1,c2: Customer | c1.password = c2.password
}

-- every password must be associated to a user or an authority
fact {
	all pw : Password | some c : Customer | pw in c.password
}

-- every customer must have a unique e-mail address
fact {
	no disj c1,c2: Customer | c1.email = c2.email
}

-- every report must generate an available notification
fact {
	all r : Report | one an : AvailableNotification | an.report = r
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

-- authorities must receive notifications of reports in their working areas 
fact {
	all r : Report, a : Authority | one an : AvailableNotification | r.municipality in a.municipalities implies
		an in a.notifications and r = an.report
}

-- municipalities must have as agents only authorities that work there
fact {
	all m : Municipality, a : Authority | m in a.municipalities iff a in m.agents
}

-- every authority works in a municipality if and only if that municipality is in his working places
fact {
	all a : Authority, m : Municipality | a in m.agents iff m in a.municipalities
}

-- every user is the author of a report if and only if that report is in his reports list
fact {
	all u : User, r : Report | u = r.author iff r in u.reports
}

-- the user must be notified of the evaluation of his reports
fact {
	all r : Report, en : EvaluatedNotification, u: User | r in u.reports and en.report = r implies en in u.notifications 
}

-- the other users must not be notified of the evaluation of reports from another user
fact {
	all r : Report, en : EvaluatedNotification, u: User | (r not in u.reports and en.report = r) 
		implies (en not in u.notifications)
}

-- every report must not produce more than one evaluated notification
fact {
	all r : Report | lone en : EvaluatedNotification | en.report = r
}
	
assert EveryReportIsReceived {
	all r : Report | some a : Authority | r in a.notifications.report
}

assert EveryEvaluationIsNotified {
	all en : EvaluatedNotification | one u : User | u = en.report.author and en in u.notifications
}

assert EveryMunicipalityIsCovered {
	all m : Municipality | some a : Authority | a in m.agents
}

pred world1 {
	#Report = 2
	#User = 2
}

check EveryReportIsReceived for 6

check EveryMunicipalityIsCovered for 6

check EveryEvaluationIsNotified for 6

run world1 for 5
