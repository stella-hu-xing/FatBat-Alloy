/*
Task1:
1. User can only have one friend and one insurer.
2. If a wearer wants to set footstep permission to False, system will remove his insurer.
3. Each emergency record will have a unique index to ensure every record could be stored.
4. System will only store the latest vitals, locations and footsteps, so each user will have at most one relative data.
*/




/** Data types **/
sig UserID {}
one sig Emergency extends UserID {} //There is exactly one emergency userID

//Three types of data stored: number of foosteps, beats per minute, and location
sig Footsteps {}
sig BPM {}
sig GPSLocation {}
sig Index{}

//A simple Boolean data type
abstract sig Boolean {}
one sig True, False extends Boolean {}

one sig NoVital extends BPM {}
one sig NoFootsteps extends Footsteps {}
one sig NoLocation extends GPSLocation {}

/** The system state **/
sig AMS {
	//The set of current users
	users : set UserID-Emergency,

	//Records each user's friend, insurer, and emergency services contact
	emergency : users->Emergency,
	friends : users-> users,
	insurers : users->users,

	//Records each user's relevant data
	footsteps : users->Footsteps,
	vitals : users->BPM,
	locations : users->GPSLocation,

	//Records permissions
	friendsFootstepPermission : friends -> one Boolean,
	friendsVitalPermission : friends -> one Boolean,
	friendsLocationPermission : friends -> one Boolean,
	emergencyFootstepPermission : emergency -> one Boolean,
	emergencyVitalPermission : emergency -> one Boolean,
	emergencyLocationPermission : emergency -> one Boolean,
	insurersFootstepPermission : insurers -> one Boolean,
	insurersVitalPermission : insurers  -> one Boolean,
	insurersLocationPermission : insurers  -> one Boolean,
	//emergency records
	emergencyRecords : Index -> users ->(BPM - NoVital) -> (GPSLocation-NoLocation)
//	emergencyRecords : Index -> users -> BPM -> GPSLocation

}
{
	//Every user has the single Emergency user as the emergency contact
	(users->Emergency) in emergency

	//Nobody can be their own friend or insurer
	all u, v : UserID | u = v implies (u->v) not in insurers+friends

	//Every user can have at most one friend
    all user1, user2, user3 : UserID | (user1->user3) in friends && (user2->user3) in friends => user1 = user2

	//Every user can have at most one insurer
	all user1, user2, user3 : UserID | (user1->user3) in insurers && (user2->user3) in insurers => user1 = user2

	//Eevry friend must have relative permissions
	all user1, user2 : UserID | (user1 -> user2) in friends => (one (user1 -> user2 -> Boolean & friendsFootstepPermission)) && (one (user1 -> user2 -> Boolean & friendsVitalPermission)) && (one (user1 -> user2 -> Boolean & friendsLocationPermission))
	
	//Every insurer must have relative permissions
	all user1, user2 : UserID | (user1 -> user2) in insurers => (one (user1 -> user2 -> True & insurersFootstepPermission)) && (one (user1 -> user2 -> Boolean& insurersVitalPermission)) && (one (user1 -> user2 -> Boolean & insurersLocationPermission))
   
	//Every user must have relative permission
    all user : users| (one (user -> Emergency -> Boolean & emergencyFootstepPermission)) &&  (one ( user -> Emergency -> Boolean & emergencyVitalPermission)) && (one (user -> Emergency -> Boolean & emergencyLocationPermission))
	
	//Every user has at most one footstep
    all user1 : users| lone user1.footsteps

	//Every user has at most vital information
	all user1 : users| lone user1.vitals

	//Every user has at most location
	all user1 : users| lone user1.locations
	//One index only match one record
	all index : Index | lone (index ->users->BPM->GPSLocation & emergencyRecords)
	//Every user has data
	all user : users | one vitals[user] && one footsteps[user] && one locations[user]


/*******************TASK2********************************************************************/
	all user1,user2 : users| (user1->user2 in friends =>user1->user2 not in insurers )&& (user1->user2 in insurers =>user1->user2 not in friends )

}

/** Initial state **/
pred init [ams : AMS] {
	no ams.users
}

/** Users and their social network **/
//Create a new user
pred CreateUser [ams, ams' : AMS, userID: one UserID] {
	userID not in ams.users
	ams'.users = ams.users + userID

	//Unchanged
	ams'.friends = ams.friends
	ams'.insurers = ams.insurers
//	DataUnchanged [ams, ams']

	ams'.vitals = ams.vitals + userID -> NoVital
	ams'.footsteps = ams.footsteps + userID -> NoFootsteps
	ams'.locations = ams.locations + userID -> NoLocation

	EmergencyRecordsUnchange[ams,ams']
	FriendPermissionUnchanged[ams,ams']
	InsurerPermissionUnchanged[ams,ams']
    //Update emergency related info
	ams'.emergency = ams.emergency + userID -> Emergency
	ams'.emergencyFootstepPermission = ams.emergencyFootstepPermission + userID -> Emergency ->True
	ams'.emergencyVitalPermission = ams.emergencyVitalPermission +  userID -> Emergency ->True
	ams'.emergencyLocationPermission = ams.emergencyLocationPermission +  userID -> Emergency ->True

}


//Update, remove, and read insurer information for a specific user
pred SetInsurer [ams, ams' : AMS, wearer, insurer: UserID] {
	wearer+insurer in ams.users
	ams'.insurers = ams.insurers ++ (wearer->insurer)

	//Unchanged
	ams'.users = ams.users
	ams'.emergency = ams.emergency
	ams'.friends = ams.friends
	DataUnchanged [ams, ams']

	EmergencyRecordsUnchange[ams,ams']
	FriendPermissionUnchanged[ams,ams']
	EmergencyPermissionUnchanged[ams,ams']
	//Update related info
    ams'.insurers = ams.insurers ++ wearer -> insurer
	ams'.insurersFootstepPermission = ams.insurersFootstepPermission ++ wearer -> insurer -> True
	ams'.insurersVitalPermission = ams.insurersVitalPermission  ++ wearer -> insurer -> True
	ams'.insurersLocationPermission = ams.insurersLocationPermission  ++ wearer -> insurer -> True
	
}

pred RemoveInsurer [ams, ams' : AMS, wearer : UserID] {
	some ams.insurers[wearer]
	ams'.insurers = ams.insurers - (wearer->UserID)

	//Unchanged
	ams'.users = ams.users
	ams'.emergency = ams.emergency
	ams'.friends = ams.friends
	DataUnchanged [ams, ams']
	EmergencyRecordsUnchange[ams,ams']

	FriendPermissionUnchanged[ams,ams']
	EmergencyPermissionUnchanged[ams,ams']
	//Update related info
	ams'.insurersFootstepPermission = ams.insurersFootstepPermission - wearer ->UserID->Boolean 
	ams'.insurersVitalPermission = ams.insurersVitalPermission  - wearer ->UserID->Boolean 
	ams'.insurersLocationPermission = ams.insurersLocationPermission  - wearer ->UserID->Boolean 
	
}

fun ReadInsurer [ams : AMS, wearer : UserID] : lone UserID {
	ams.insurers[wearer]
}

//Update, remove, and read friend information for a specific user
pred SetFriend [ams, ams' : AMS, wearer, friend: UserID] {
	wearer+friend in ams.users
	ams'.friends = ams.friends ++ (wearer->friend)

	//Unchanged:
	ams'.users = ams.users
	ams'.emergency = ams.emergency
	ams'.insurers = ams.insurers
	DataUnchanged [ams, ams']

	InsurerPermissionUnchanged[ams,ams']
	EmergencyPermissionUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
	//Update related info
	ams'.friendsFootstepPermission = ams.friendsFootstepPermission ++  wearer -> friend -> True
	ams'.friendsVitalPermission =ams.friendsVitalPermission ++  wearer -> friend -> True 
	ams'.friendsLocationPermission =	ams.friendsLocationPermission ++  wearer -> friend -> True 
	
}

pred RemoveFriend [ams, ams' : AMS, wearer : UserID] {
	some ams.friends[wearer]
	ams'.friends = ams.friends - (wearer->UserID)
	
	//Unchanged:
	ams'.users = ams.users
	ams'.emergency = ams.emergency
	ams'.insurers = ams.insurers
	DataUnchanged [ams, ams']

	EmergencyRecordsUnchange[ams,ams']
	InsurerPermissionUnchanged[ams,ams']
	EmergencyPermissionUnchanged[ams,ams']
	//Update related info
	ams'.friendsFootstepPermission = ams.friendsFootstepPermission - wearer ->UserID -> Boolean
	ams'.friendsVitalPermission =ams.friendsVitalPermission - wearer ->UserID -> Boolean
	ams'.friendsLocationPermission =	ams.friendsLocationPermission - wearer ->UserID -> Boolean
	
}

fun ReadFriend [ams : AMS, wearer : UserID] : lone UserID {
	ams.friends[wearer]
}

/** Data management **/
//Update relevant data
pred UpdateFootsteps [ams, ams' : AMS, wearer : UserID, newFootsteps : Footsteps] {
	wearer in ams.users
	ams'.footsteps = ams.footsteps ++ (wearer->newFootsteps)

	//Unchanged:
	ams'.vitals = ams.vitals
	ams'.locations = ams.locations
	UsersUnchanged [ams, ams']
	PermissionUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
}

pred UpdateVitals [ams, ams' : AMS, wearer : UserID, newVitals : BPM] {
	wearer in ams.users
	ams'.vitals = ams.vitals ++ (wearer->newVitals)

	//Unchanged:
	ams'.footsteps = ams.footsteps
	ams'.locations = ams.locations
	UsersUnchanged [ams, ams']
	PermissionUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
}

pred UpdateLocation [ams, ams' : AMS, wearer : UserID, newLocation : GPSLocation] {
	wearer in ams.users
	ams'.locations = ams.locations ++ (wearer->newLocation)

	//Unchanged:
	ams'.footsteps = ams.footsteps
	ams'.vitals = ams.vitals
	UsersUnchanged [ams, ams']
	PermissionUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
}
/*************************************************************************************/

/** Permission management function**/

pred ReadFootstep[ams:AMS, requester, targetUser: UserID, returnFootstep : Footsteps]{
	requester + targetUser in ams.users
	((requester = targetUser)||(targetUser -> requester in ams.friends && GetFriendsFootstepPermission[ams,requester, targetUser] =True)||
	(targetUser -> requester in ams.insurers && GetInsurersFootstepPermission[ams,requester, targetUser] =True)||
	(targetUser -> requester in ams.emergency && GetEmergencyFootstepPermission[ams, targetUser] =True))

	returnFootstep =  ams.footsteps[targetUser]

}

pred ReadVital[ams:AMS, requester, targetUser: UserID, returenVital : BPM]{
	requester + targetUser in ams.users
	((requester = targetUser)||(targetUser -> requester in ams.friends && GetFriendsVitalPermission[ams,requester, targetUser] =True)||
	(targetUser -> requester in ams.insurers && GetInsurersVitalPermission[ams,requester, targetUser] =True)||
	(targetUser -> requester in ams.emergency && GetEmergencyVitalPermission[ams, targetUser] =True))

	returenVital =  ams.vitals[targetUser]

}

pred ReadLocation[ams:AMS, requester, targetUser: UserID, returenLocation : GPSLocation]{
	requester + targetUser in ams.users
	((requester = targetUser)||(targetUser -> requester in ams.friends && GetFriendsLocationPermission[ams,requester, targetUser] =True)||
	(targetUser -> requester in ams.insurers && GetInsurersLocationPermission[ams,requester, targetUser] =True)||
	(targetUser -> requester in ams.emergency && GetEmergencyLocationPermission[ams, targetUser] =True))

	returenLocation =  ams.locations[targetUser]

}



/*----------------------------Unchanged_permissions---------------------------------*/
pred PermissionUnchanged[ams,ams' : AMS]{
   ams'.friendsLocationPermission = ams.friendsLocationPermission
   ams'.friendsFootstepPermission = ams.friendsFootstepPermission
   ams'.friendsVitalPermission = ams.friendsVitalPermission

   ams'.insurersLocationPermission = ams.insurersLocationPermission
   ams'.insurersFootstepPermission = ams.insurersFootstepPermission
   ams'.insurersVitalPermission = ams.insurersVitalPermission

	ams'.emergencyLocationPermission = ams.emergencyLocationPermission
	ams'.emergencyFootstepPermission = ams.emergencyFootstepPermission
	ams'.emergencyVitalPermission = ams.emergencyVitalPermission
}

pred FootstepsPermissionUnchanged[ams,ams': AMS]{
    ams'.friendsFootstepPermission = ams.friendsFootstepPermission
    ams'.insurersFootstepPermission = ams. insurersFootstepPermission
    ams'.emergencyFootstepPermission = ams.emergencyFootstepPermission
}

pred VitalPermissionUnchanged[ams,ams': AMS]{
    ams'.friendsVitalPermission = ams.friendsVitalPermission
    ams'.insurersVitalPermission = ams. insurersVitalPermission
    ams'.emergencyVitalPermission = ams.emergencyVitalPermission
}

pred LocationPermissionUnchanged[ams,ams': AMS]{
    ams'.friendsLocationPermission = ams.friendsLocationPermission
    ams'.insurersLocationPermission = ams. insurersLocationPermission
    ams'.emergencyLocationPermission = ams.emergencyLocationPermission
}

pred FriendPermissionUnchanged[ams,ams': AMS]{
   ams'.friendsLocationPermission = ams.friendsLocationPermission
   ams'.friendsFootstepPermission = ams.friendsFootstepPermission
   ams'.friendsVitalPermission = ams.friendsVitalPermission
}

pred InsurerPermissionUnchanged[ams,ams': AMS]{
   ams'.insurersLocationPermission = ams.insurersLocationPermission
   ams'.insurersFootstepPermission = ams.insurersFootstepPermission
   ams'.insurersVitalPermission = ams.insurersVitalPermission
}

pred EmergencyPermissionUnchanged[ams,ams': AMS]{
   ams'.emergencyLocationPermission = ams.emergencyLocationPermission
   ams'.emergencyFootstepPermission = ams.emergencyFootstepPermission
   ams'.emergencyVitalPermission = ams.emergencyVitalPermission
}

// Get permissions
fun GetFriendsFootstepPermission[ams : AMS, requester, targetUser : UserID] : lone Boolean{
	ams.friendsFootstepPermission[targetUser][requester]
}

fun GetFriendsVitalPermission[ams : AMS, requester, targetUser : UserID] : lone Boolean{
	ams.friendsVitalPermission[targetUser][requester]
}

fun GetFriendsLocationPermission[ams : AMS, requester, targetUser : UserID] : lone Boolean{
	ams.friendsLocationPermission[targetUser][requester]
}


fun GetInsurersFootstepPermission[ams : AMS, requester, targetUser : UserID] : lone Boolean{
	ams.insurersFootstepPermission[targetUser][requester]
}
fun GetInsurersVitalPermission[ams : AMS, requester, targetUser : UserID] : lone Boolean{
	ams.insurersVitalPermission[targetUser][requester]
}

fun GetInsurersLocationPermission[ams : AMS, requester, targetUser : UserID] : lone Boolean{
	ams.insurersLocationPermission[targetUser][requester]
}

fun GetEmergencyFootstepPermission[ams : AMS, targetUser: UserID] : lone Boolean{
	ams.emergencyFootstepPermission[targetUser][Emergency]
}

fun GetEmergencyVitalPermission[ams : AMS, targetUser : UserID] : lone Boolean{
	ams.emergencyVitalPermission[targetUser][Emergency]
}

fun GetEmergencyLocationPermission[ams : AMS, targetUser : UserID] : lone Boolean{
	ams.emergencyLocationPermission[targetUser][Emergency]
}

/*--------------------------Update_Permission-------------------------------*/

pred UpdateFriendFootstepPermission[ams,ams': AMS, userID, friendID : UserID, newAllow : Boolean]{

	userID -> friendID in ams.friends

   	ams'.friendsFootstepPermission = ams.friendsFootstepPermission ++ (userID -> friendID->newAllow)
    
   //unchange
	UsersUnchanged[ams,ams']
	DataUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
    InsurerPermissionUnchanged[ams,ams']
    EmergencyPermissionUnchanged[ams,ams']
    ams'.friendsVitalPermission = ams.friendsVitalPermission
	ams'.friendsLocationPermission = ams.friendsLocationPermission
    
}

pred UpdateFriendVitalPermission[ams,ams': AMS, userID, friendID : UserID, newAllow : Boolean]{

	userID -> friendID in ams.friends

   	ams'.friendsVitalPermission = ams.friendsVitalPermission ++ (userID -> friendID->newAllow)
    
   //unchange
	UsersUnchanged[ams,ams']
	DataUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
    InsurerPermissionUnchanged[ams,ams']
    EmergencyPermissionUnchanged[ams,ams']
    ams'.friendsFootstepPermission = ams.friendsFootstepPermission
	ams'.friendsLocationPermission = ams.friendsLocationPermission
    
}

pred UpdateFriendLocationPermission[ams,ams': AMS,userID, friendID : UserID, newAllow : Boolean]{

	userID -> friendID in ams.friends

   	ams'.friendsLocationPermission = ams.friendsLocationPermission ++ (userID -> friendID->newAllow)
    
   //unchange
	UsersUnchanged[ams,ams']
	DataUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
    InsurerPermissionUnchanged[ams,ams']
    EmergencyPermissionUnchanged[ams,ams']
    ams'.friendsFootstepPermission = ams.friendsFootstepPermission
	ams'.friendsVitalPermission = ams.friendsVitalPermission
    
}
//******Insurer must have permission to read footsteps**********/

pred SetInsurerFootstepsPermissionTrue[ams,ams' : AMS ,userID ,insurerID : UserID] {

	userID -> insurerID in ams.insurers

   	ams'.insurersFootstepPermission = ams.insurersFootstepPermission ++ (userID -> insurerID->True)
    
   //unchange
	UsersUnchanged[ams,ams']
	DataUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
    FriendPermissionUnchanged[ams,ams']
    EmergencyPermissionUnchanged[ams,ams']
	ams'.insurersVitalPermission = ams.insurersVitalPermission
	ams'.insurersLocationPermission = ams.insurersLocationPermission

}

pred SetInsurerFootstepsPermissionFalse[ams, ams' : AMS, userID,insurerID : UserID] {
	some ams.insurers[userID]
	ams'.insurers = ams.insurers - (userID->insurerID)

	//Unchanged
	ams'.users = ams.users
	ams'.emergency = ams.emergency
	ams'.friends = ams.friends
	DataUnchanged [ams, ams']
	EmergencyRecordsUnchange[ams,ams']
	FriendPermissionUnchanged[ams,ams']
	EmergencyPermissionUnchanged[ams,ams']
	//Update related info
	ams'.insurersFootstepPermission = ams.insurersFootstepPermission - userID ->insurerID->Boolean 
	ams'.insurersVitalPermission = ams.insurersVitalPermission  - userID ->insurerID->Boolean 
	ams'.insurersLocationPermission = ams.insurersLocationPermission  - userID ->insurerID->Boolean 
	
}
pred UpdateInsurerFootstepPermission[ams,ams':AMS, userID,insurerID : UserID, permission: Boolean]{
 	( permission = True && SetInsurerFootstepsPermissionTrue[ams,ams',userID,insurerID]) or 
	( permission = False && SetInsurerFootstepsPermissionFalse[ams,ams',userID,insurerID])
}

//run UpdateInsurerFootstepPermission for 5 but 2 AMS

pred UpdateInsurerVitalPermission[ams,ams': AMS, userID, insurerID : UserID, newAllow : Boolean]{

	userID -> insurerID in ams.insurers

   	ams'.insurersVitalPermission = ams.insurersVitalPermission ++ (userID -> insurerID->newAllow)
    
   //unchange
	UsersUnchanged[ams,ams']
	DataUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
    FriendPermissionUnchanged[ams,ams']
    EmergencyPermissionUnchanged[ams,ams']
	ams'.insurersFootstepPermission = ams.insurersFootstepPermission
	ams'.insurersLocationPermission = ams.insurersLocationPermission
    
}


pred UpdateInsurerLocationPermission[ams,ams': AMS, userID, insurerID : UserID, newAllow : Boolean]{

	userID -> insurerID in ams.insurers

   	ams'.insurersLocationPermission = ams.insurersLocationPermission ++ (userID -> insurerID->newAllow)
    
   //unchange
	UsersUnchanged[ams,ams']
	DataUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
    FriendPermissionUnchanged[ams,ams']
    EmergencyPermissionUnchanged[ams,ams']
	ams'.insurersFootstepPermission = ams.insurersFootstepPermission
	ams'.insurersVitalPermission = ams.insurersVitalPermission
    
}

pred UpdateEmergencyFootstepPermission[ams,ams': AMS, userID : UserID, newAllow : Boolean]{

	userID -> Emergency in ams.emergency

   	ams'.emergencyFootstepPermission = ams.emergencyFootstepPermission ++ (userID ->Emergency ->newAllow)
    
   //unchange
	UsersUnchanged[ams,ams']
	DataUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
    FriendPermissionUnchanged[ams,ams']
    InsurerPermissionUnchanged[ams,ams']
	ams'.emergencyVitalPermission = ams.emergencyVitalPermission
	ams'.emergencyLocationPermission = ams.emergencyLocationPermission
    
}

pred UpdateEmergencyVitalPermission[ams,ams': AMS, userID : UserID, newAllow : Boolean]{

	userID ->Emergency  in ams.emergency

   	ams'.emergencyVitalPermission = ams.emergencyVitalPermission ++ (userID ->Emergency ->newAllow)
    
   //unchange
	UsersUnchanged[ams,ams']
	DataUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
    FriendPermissionUnchanged[ams,ams']
    InsurerPermissionUnchanged[ams,ams']
	ams'.emergencyFootstepPermission = ams.emergencyFootstepPermission
	ams'.emergencyLocationPermission = ams.emergencyLocationPermission
    
}


pred UpdateEmergencyLocationPermission[ams,ams': AMS, userID: UserID, newAllow : Boolean]{

    userID ->Emergency  in ams.emergency

   	ams'.emergencyLocationPermission = ams.emergencyLocationPermission ++ ( userID ->Emergency ->newAllow)
    
   //unchange
	UsersUnchanged[ams,ams']
	DataUnchanged[ams,ams']
	EmergencyRecordsUnchange[ams,ams']
    FriendPermissionUnchanged[ams,ams']
    InsurerPermissionUnchanged[ams,ams']
	ams'.emergencyFootstepPermission = ams.emergencyFootstepPermission
	ams'.emergencyVitalPermission = ams.emergencyVitalPermission
    
}


pred ContactEmergency[ams,ams',ams'',ams''' : AMS, wearer : UserID, index : one Index, newBPM : BPM, newGPS : GPSLocation]{
	GetEmergencyVitalPermission[ams, wearer] = True 
	one ams.vitals[wearer]
	one ams.locations[wearer]

	ExternalContactEmergency[wearer, newGPS, newBPM]
	UpdateVitals [ams, ams', wearer, newBPM]
	UpdateLocation[ams', ams'', wearer, newGPS]
 	no (index ->UserID->BPM->GPSLocation & ams''.emergencyRecords)
	ams'''.emergencyRecords = ams''.emergencyRecords +(index ->wearer->newBPM->newGPS)
   //unchange
	UsersUnchanged[ams'',ams''']
	DataUnchanged[ams'',ams''']
	PermissionUnchanged[ams'',ams''']

}
run ContactEmergency for 6

assert CheckVoidVitalEmergency{
	all ams1,ams2,ams3,ams4:AMS,wearer:UserID,index1:Index|
	wearer in ams1.users&& (ams1.vitals[wearer] != NoVital) && (ams1.locations[wearer] != NoLocation)
	&&ContactEmergency[ams1,ams2,ams3,ams4,wearer,index1,NoVital,NoLocation]
	=>index1->wearer->NoVital->NoLocation not in ams4.emergencyRecords
}
check CheckVoidVitalEmergency for 6

assert CheckvoidvitalEmergencyAgain{
	all ams : AMS|
	some ams.emergencyRecords =>(no ((Index->UserID->NoVital -> NoLocation)& ams.emergencyRecords))
                                                    && (no ((Index->UserID->NoVital -> GPSLocation)& ams.emergencyRecords))
                                                   	&& (no ((Index->UserID->BPM -> NoLocation)& ams.emergencyRecords)) 
}

check CheckvoidvitalEmergencyAgain for 3

pred EmergencyRecordsUnchange[ams,ams' : AMS]{
	ams.emergencyRecords = ams'.emergencyRecords
}
/*************************************************************************************/


/** Models of "external" API calls **/
//ContactEmergency -- The external call specified in the 'Emergency' package in Assignment 1
pred ExternalContactEmergency [wearer : UserID, wearerLocation : GPSLocation, wearerVitals : BPM] {
	//Contact emergency services
}

/** Helper predicates **/
//Users and their social network are unchanged
pred UsersUnchanged [ams, ams' : AMS] {
	ams'.users = ams.users
	ams'.emergency = ams.emergency
	ams'.friends = ams.friends
	ams'.insurers = ams.insurers
}

//Data about users isunchanged
pred DataUnchanged [ams, ams' : AMS] {
	ams'.footsteps = ams.footsteps
	ams'.vitals = ams.vitals
	ams'.locations = ams.locations
}

run CreateUser for 4
assert NoUnpermitedReadFootsteps{
	no ams: AMS, requester, targetUser: UserID, foots : Footsteps |
	((requester != targetUser) && (GetFriendsFootstepPermission[ams,requester,targetUser] = False) &&  (GetInsurersFootstepPermission[ams,requester, targetUser] = False)
	 && ( GetEmergencyFootstepPermission[ams, targetUser] = False)) && (ReadFootstep[ams, requester, targetUser, foots])
}

check NoUnpermitedReadFootsteps for 3



assert NoUnpermitedReadVitals{
	no ams: AMS, requester, targetUser: UserID, vital : BPM|
	((requester != targetUser) && (GetFriendsVitalPermission[ams,requester,targetUser] = False) && (GetInsurersVitalPermission[ams,requester, targetUser] = False)
	 && ( GetEmergencyVitalPermission[ams, targetUser] = False)) && (ReadVital[ams, requester, targetUser, vital])
}

check NoUnpermitedReadVitals for 3

assert NoUnpermitedReadLocations{
	no ams: AMS, requester, targetUser: UserID, gps : GPSLocation|
	((requester != targetUser) && (GetFriendsLocationPermission[ams,requester,targetUser] = False) && (GetInsurersLocationPermission[ams,requester, targetUser] = False)
	 && ( GetEmergencyLocationPermission[ams, targetUser] = False)) && (ReadLocation[ams, requester, targetUser, gps])
}

check NoUnpermitedReadLocations for 3

//Creating a new user does not add any friends/insurers
assert NoUserChange {
	all ams, ams' : AMS, userID : UserID | 
		CreateUser[ams, ams', userID] => ams.friends = ams'.friends and ams.insurers = ams'.insurers
}
check NoUserChange for 3


assert TestUpdateInsurerFootstepPermission{
 all ams,ams',ams'',ams''',ams'''',ams''''' : AMS, user1,user2:UserID, footstep: Footsteps |
	CreateUser [ams, ams', user1] && CreateUser[ams',ams'',user2]&&SetInsurer[ams'',ams''',user1,user2]&&
 UpdateFootsteps[ams''',ams'''',user1, footstep]&&UpdateInsurerFootstepPermission[ams'''',ams''''',user1,user2,False] => (user1->user2->False in ams'''''.insurersFootstepPermission) 
}
check TestUpdateInsurerFootstepPermission for 6


assert TestEmergencyRecords{
	all ams1,ams2,ams3,ams4,ams5,ams6,ams7 : AMS, user1,user2:UserID,index1,index2:Index,bpm1,bpm2:BPM, gps1,gps2:GPSLocation|	
	ContactEmergency[ams1,ams2, ams3,ams4,user1,index1,bpm1,gps1] && ContactEmergency[ams4,ams5,ams6,ams7,user2,index2,bpm2,gps2]=> index1 != index2
}

check TestEmergencyRecords for 6


/* Task 2 : Check if user1 is both friend and insurer of user2 and have different permissions for one type of data.*/
assert CheckMultiplePermission{

	all ams,ams1,ams2,ams3,ams4,ams5,ams6:AMS, wearer, user: UserID, location: GPSLocation|
	CreateUser[ams, ams1, wearer]&&CreateUser[ams1,ams2, user]&&
	SetInsurer[ams2, ams3, wearer,user]&&UpdateInsurerLocationPermission[ams3,ams4, wearer,user,True]
	&&SetFriend[ams4, ams5, wearer, user]&&UpdateFriendLocationPermission[ams5,ams6,wearer,user,False]
	=> ReadLocation[ams, user,wearer,location]
}
check CheckMultiplePermission for 7
