import LeanEff
import SQLite
import Std.Time

open LeanEff

namespace Examples.VideoRental

abbrev Day := Nat

structure Config where
  shopName : String
deriving Inhabited, Repr

structure Customer where
  id : Nat
  name : String
  email : String
deriving BEq, Inhabited, Repr

structure Movie where
  id : Nat
  title : String
deriving BEq, Inhabited, Repr

structure RentalDraft where
  customerId : Nat
  movieId : Nat
  rentedDay : Day
  dueDay : Day
deriving Inhabited, Repr

structure ExpiredRental where
  rentalId : Nat
  customerName : String
  email : String
  movieTitle : String
  dueDay : Day
  today : Day
deriving Inhabited, Repr

inductive ShopError where
  | unknownCustomer : Nat → ShopError
  | unknownMovie : Nat → ShopError
  | invalidPeriod : Nat → ShopError
deriving Inhabited, Repr

inductive Clock : Effect where
  | today : Clock Day

def today {r : List Effect} [Member Clock r] : Eff r Day :=
  send Clock.today

def runClockAt {α : Type} {r r' : List Effect} [Remove Clock r r']
    [Inhabited α]
    (day : Day) : Eff r α → Eff r' α :=
  handleRelay (t := Clock)
    (ret := fun x => pure x)
    (handle := fun request k =>
      match request with
      | Clock.today => k day)

inductive Console : Effect where
  | printLine : String → Console Unit
  | readLine : Console String

def printLine {r : List Effect} [Member Console r]
    (line : String) : Eff r Unit :=
  send (Console.printLine line)

def readInput {r : List Effect} [Member Console r] : Eff r String :=
  send Console.readLine

inductive RentalRepo : Effect where
  | findCustomer : Nat → RentalRepo (Option Customer)
  | findMovie : Nat → RentalRepo (Option Movie)
  | createRental : RentalDraft → RentalRepo Unit
  | expiredRentals : Day → RentalRepo (List ExpiredRental)
  | markNotified : Nat → RentalRepo Unit
  | listCustomers : RentalRepo (List Customer)
  | listMovies : RentalRepo (List Movie)

def findCustomer {r : List Effect} [Member RentalRepo r]
    (id : Nat) : Eff r (Option Customer) :=
  send (RentalRepo.findCustomer id)

def findMovie {r : List Effect} [Member RentalRepo r]
    (id : Nat) : Eff r (Option Movie) :=
  send (RentalRepo.findMovie id)

def createRental {r : List Effect} [Member RentalRepo r]
    (rental : RentalDraft) : Eff r Unit :=
  send (RentalRepo.createRental rental)

def expiredRentals {r : List Effect} [Member RentalRepo r]
    (day : Day) : Eff r (List ExpiredRental) :=
  send (RentalRepo.expiredRentals day)

def markNotified {r : List Effect} [Member RentalRepo r]
    (rentalId : Nat) : Eff r Unit :=
  send (RentalRepo.markNotified rentalId)

def listCustomers {r : List Effect} [Member RentalRepo r] : Eff r (List Customer) :=
  send RentalRepo.listCustomers

def listMovies {r : List Effect} [Member RentalRepo r] : Eff r (List Movie) :=
  send RentalRepo.listMovies

abbrev ShopEff (α : Type) :=
  Eff [Reader Config, Clock, RentalRepo, Writer String, ExceptE ShopError, Console] α

def formatDay (day : Day) : String :=
  s!"day {day}"

def repeatString (s : String) (n : Nat) : String :=
  String.intercalate "" ((List.range n).map fun _ => s)

def clip (width : Nat) (text : String) : String :=
  if text.length <= width then
    text
  else if width <= 3 then
    (text.take width).toString
  else
    (text.take (width - 3)).toString ++ "..."

def padRight (width : Nat) (text : String) : String :=
  let text := clip width text
  text ++ repeatString " " (width - text.length)

def frameLine (width : Nat) (left mid right : String) : String :=
  left ++ repeatString mid width ++ right

def box (title : String) (lines : List String) : List String :=
  let width := 72
  [frameLine width "+" "-" "+",
   "| " ++ padRight (width - 2) title ++ " |",
   frameLine width "+" "-" "+"] ++
  (lines.map fun line => "| " ++ padRight (width - 2) line ++ " |") ++
  [frameLine width "+" "-" "+"]

def printBox (title : String) (lines : List String) : ShopEff Unit := do
  for line in box title lines do
    printLine line

def tableLine (widths : List Nat) : String :=
  "+" ++ String.intercalate "+" (widths.map fun width => repeatString "-" (width + 2)) ++ "+"

def tableRow (widths : List Nat) (cells : List String) : String :=
  let pairs := widths.zip cells
  "| " ++ String.intercalate " | " (pairs.map fun (width, cell) => padRight width cell) ++ " |"

def printTable (title : String) (widths : List Nat) (header : List String)
    (rows : List (List String)) : ShopEff Unit := do
  printLine ""
  printLine title
  printLine (tableLine widths)
  printLine (tableRow widths header)
  printLine (tableLine widths)
  for row in rows do
    printLine (tableRow widths row)
  printLine (tableLine widths)

def splashLines : List String :=
  [" ____       _ _           _ _      _",
   "|  _ \\ __ _| | | __ _  __| (_)_ __( )___",
   "| |_) / _` | | |/ _` |/ _` | | '_ \\// __|",
   "|  __/ (_| | | | (_| | (_| | | | | |\\__ \\",
   "|_|   \\__,_|_|_|\\__,_|\\__,_|_|_| |_|___/",
   "        V I D E O   R E N T A L   D E S K"]

def printSplash : ShopEff Unit :=
  printBox "Palladin's Video Rental" splashLines

def emit (message : String) : ShopEff Unit := do
  tell message
  printLine message

def requireCustomer (id : Nat) : ShopEff Customer := do
  match (← findCustomer id) with
  | some customer => pure customer
  | none => LeanEff.throw (ShopError.unknownCustomer id)

def requireMovie (id : Nat) : ShopEff Movie := do
  match (← findMovie id) with
  | some movie => pure movie
  | none => LeanEff.throw (ShopError.unknownMovie id)

def rentMovie (customerId movieId periodDays : Nat) : ShopEff Unit := do
  if periodDays > 30 then
    LeanEff.throw (ShopError.invalidPeriod periodDays)
  let customer ← requireCustomer customerId
  let movie ← requireMovie movieId
  let rented ← today
  let due := rented + periodDays
  createRental
    { customerId := customer.id
      movieId := movie.id
      rentedDay := rented
      dueDay := due }
  emit s!"{customer.name} rented \"{movie.title}\" until {formatDay due}"

def notification (rental : ExpiredRental) : String :=
  s!"notify {rental.customerName} <{rental.email}>: \"{rental.movieTitle}\" was due on {formatDay rental.dueDay}"

def notifyExpired : ShopEff Nat := do
  let day ← today
  let expired ← expiredRentals day
  for rental in expired do
    emit (notification rental)
    markNotified rental.rentalId
  pure expired.length

def showCatalog : ShopEff Unit := do
  let movies ← listMovies
  if movies.isEmpty then
    printBox "Movies" ["No movies in the catalog."]
  else
    printTable "Movies" [6, 42] ["ID", "Title"] <|
      movies.map fun movie => [toString movie.id, movie.title]

def showCustomers : ShopEff Unit := do
  let customers ← listCustomers
  if customers.isEmpty then
    printBox "Customers" ["No customers registered."]
  else
    printTable "Customers" [6, 18, 32] ["ID", "Name", "Email"] <|
      customers.map fun customer => [toString customer.id, customer.name, customer.email]

def prompt (label : String) : ShopEff String := do
  printLine s!"> {label}"
  readInput

def promptNat (label : String) : ShopEff (Option Nat) := do
  let value ← prompt label
  pure value.trimAscii.toString.toNat?

def rentFromMenu : ShopEff Unit := do
  printBox "New Rental" ["Select a customer, a movie, and the rental period."]
  showCustomers
  showCatalog
  match (← promptNat "Customer id") with
  | none => printBox "Input Error" ["Please enter a numeric customer id."]
  | some customerId =>
      match (← promptNat "Movie id") with
      | none => printBox "Input Error" ["Please enter a numeric movie id."]
      | some movieId =>
          match (← promptNat "Rental period in days") with
          | none => printBox "Input Error" ["Please enter a numeric rental period."]
          | some periodDays => rentMovie customerId movieId periodDays

def notifyExpiredFromMenu : ShopEff Unit := do
  let count ← notifyExpired
  if count == 0 then
    printBox "Notifications" ["No expired rentals need notification."]
  else
    printBox "Notifications" [s!"Queued {count} notification(s)."]

def handleShopError (action : ShopEff Unit) : ShopEff Unit :=
  tryCatch (ε := ShopError) action fun error => do
    let message :=
      match error with
      | .unknownCustomer id => s!"Unknown customer #{id}."
      | .unknownMovie id => s!"Unknown movie #{id}."
      | .invalidPeriod days => s!"Invalid rental period: {days} day(s)."
    tell message
    printBox "Error" [message]

def printMenu : ShopEff Unit := do
  printBox "Main Menu"
    ["1  List movies",
     "2  List customers",
     "3  Rent a movie",
     "4  Notify expired rentals",
     "q  Quit"]

partial def menuLoop (_ : Unit) : ShopEff Unit := do
  printMenu
  let choice ← prompt "Choose an option:"
  match choice.trimAscii.toString with
  | "1" => do
      handleShopError showCatalog
      menuLoop ()
  | "2" => do
      handleShopError showCustomers
      menuLoop ()
  | "3" => do
      handleShopError rentFromMenu
      menuLoop ()
  | "4" => do
      handleShopError notifyExpiredFromMenu
      menuLoop ()
  | "q" => do
      emit "Closing Palladin's Video Rental."
  | "Q" => do
      emit "Closing Palladin's Video Rental."
  | _ => do
      printBox "Menu" ["Unknown option."]
      menuLoop ()

def appProgram : ShopEff Unit := do
  let cfg ← ask (ρ := Config)
  printSplash
  emit s!"Welcome to {cfg.shopName}"
  printBox "Demo Store" ["The in-memory SQLite database has been populated with demo data."]
  menuLoop ()

def previousDay (day : Day) : Day :=
  if day == 0 then 0 else day - 1

def tenDaysAgo (day : Day) : Day :=
  if day < 10 then 0 else day - 10

def sqlString (value : String) : String :=
  "'" ++ value.replace "'" "''" ++ "'"

def sqlNat (value : Nat) : String :=
  toString value

structure SqliteConn where
  db : SQLite

def columnNat (stmt : SQLite.Stmt) (column : Int32) : IO Nat := do
  let value ← stmt.columnText column
  match value.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"expected Nat in SQLite column {column}, got {value}")

def readCustomer (stmt : SQLite.Stmt) : IO Customer := do
  let id ← columnNat stmt 0
  let name ← stmt.columnText 1
  let email ← stmt.columnText 2
  pure { id, name, email }

def readMovie (stmt : SQLite.Stmt) : IO Movie := do
  let id ← columnNat stmt 0
  let title ← stmt.columnText 1
  pure { id, title }

def readExpired (day : Day) (stmt : SQLite.Stmt) : IO ExpiredRental := do
  let rentalId ← columnNat stmt 0
  let customerName ← stmt.columnText 1
  let email ← stmt.columnText 2
  let movieTitle ← stmt.columnText 3
  let dueDay ← columnNat stmt 4
  pure { rentalId, customerName, email, movieTitle, dueDay, today := day }

partial def queryRows
    (conn : SqliteConn) (sql : String) (read : SQLite.Stmt → IO α) :
    IO (List α) := do
  let stmt ← conn.db.prepare sql
  let rec loop (acc : List α) : IO (List α) := do
    if (← stmt.step) then
      let row ← read stmt
      loop (row :: acc)
    else
      pure acc.reverse
  loop []

def sqliteExec (conn : SqliteConn) (sql : String) : IO Unit :=
  conn.db.exec sql

def openInMemorySqlite : IO SqliteConn := do
  let db ← SQLite.openWith (":memory:" : System.FilePath)
    { SQLite.OpenFlags.readWriteCreate with memory := true }
  pure { db }

def initSql (day : Day) : String :=
  let oldRented := tenDaysAgo day
  let oldDue := previousDay day
  String.intercalate "\n"
    ["CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT NOT NULL, email TEXT NOT NULL);",
     "CREATE TABLE movies(id INTEGER PRIMARY KEY, title TEXT NOT NULL);",
     "CREATE TABLE rentals(id INTEGER PRIMARY KEY AUTOINCREMENT, customer_id INTEGER NOT NULL, movie_id INTEGER NOT NULL, rented_day INTEGER NOT NULL, due_day INTEGER NOT NULL, returned_day INTEGER, notified INTEGER NOT NULL DEFAULT 0);",
     s!"INSERT INTO customers(id, name, email) VALUES (1, {sqlString "Ada"}, {sqlString "ada@palladins.example"});",
     s!"INSERT INTO customers(id, name, email) VALUES (2, {sqlString "Grace"}, {sqlString "grace@palladins.example"});",
     s!"INSERT INTO customers(id, name, email) VALUES (3, {sqlString "Nikos"}, {sqlString "nikos@palladins.example"});",
     s!"INSERT INTO movies(id, title) VALUES (10, {sqlString "The Matrix"});",
     s!"INSERT INTO movies(id, title) VALUES (11, {sqlString "Spirited Away"});",
     s!"INSERT INTO movies(id, title) VALUES (12, {sqlString "The Maltese Falcon"});",
     s!"INSERT INTO rentals(customer_id, movie_id, rented_day, due_day) VALUES (3, 12, {sqlNat oldRented}, {sqlNat oldDue});"]

def findCustomerSqlite (conn : SqliteConn) (id : Nat) : IO (Option Customer) := do
  let rows ← queryRows conn
    s!"SELECT id, name, email FROM customers WHERE id = {sqlNat id} LIMIT 1;"
    readCustomer
  pure rows.head?

def findMovieSqlite (conn : SqliteConn) (id : Nat) : IO (Option Movie) := do
  let rows ← queryRows conn
    s!"SELECT id, title FROM movies WHERE id = {sqlNat id} LIMIT 1;"
    readMovie
  pure rows.head?

def createRentalSqlite (conn : SqliteConn) (rental : RentalDraft) : IO Unit := do
  sqliteExec conn
    s!"INSERT INTO rentals(customer_id, movie_id, rented_day, due_day) VALUES ({sqlNat rental.customerId}, {sqlNat rental.movieId}, {sqlNat rental.rentedDay}, {sqlNat rental.dueDay});"

def expiredRentalsSqlite (conn : SqliteConn) (day : Day) : IO (List ExpiredRental) := do
  queryRows conn
    s!"SELECT rentals.id, customers.name, customers.email, movies.title, rentals.due_day FROM rentals JOIN customers ON customers.id = rentals.customer_id JOIN movies ON movies.id = rentals.movie_id WHERE rentals.returned_day IS NULL AND rentals.notified = 0 AND rentals.due_day <= {sqlNat day} ORDER BY rentals.due_day, rentals.id;"
    (readExpired day)

def markNotifiedSqlite (conn : SqliteConn) (rentalId : Nat) : IO Unit := do
  sqliteExec conn
    s!"UPDATE rentals SET notified = 1 WHERE id = {sqlNat rentalId};"

def listCustomersSqlite (conn : SqliteConn) : IO (List Customer) := do
  queryRows conn "SELECT id, name, email FROM customers ORDER BY name;" readCustomer

def listMoviesSqlite (conn : SqliteConn) : IO (List Movie) := do
  queryRows conn "SELECT id, title FROM movies ORDER BY title;" readMovie

def currentUnixDay : IO Day := do
  let timestamp ← Std.Time.Timestamp.now
  let seconds := timestamp.toSecondsSinceUnixEpoch.val
  if seconds < 0 then
    pure 0
  else
    pure (seconds.toNat / 86400)

partial def runShopIO {α : Type}
    (conn : SqliteConn) : Eff [Clock, RentalRepo, Console] α → IO α
  | Eff.pure x => pure x
  | Eff.impure u q =>
      match u with
      | OpenUnion.here request =>
          match request with
          | Clock.today => do
              let day ← currentUnixDay
              runShopIO conn (Arrs.apply q day)
      | OpenUnion.there repoUnion =>
          match repoUnion with
          | OpenUnion.here request =>
              match request with
              | RentalRepo.findCustomer id => do
                  let customer ← findCustomerSqlite conn id
                  runShopIO conn (Arrs.apply q customer)
              | RentalRepo.findMovie id => do
                  let movie ← findMovieSqlite conn id
                  runShopIO conn (Arrs.apply q movie)
              | RentalRepo.createRental rental => do
                  createRentalSqlite conn rental
                  runShopIO conn (Arrs.apply q ())
              | RentalRepo.expiredRentals expiredDay => do
                  let rentals ← expiredRentalsSqlite conn expiredDay
                  runShopIO conn (Arrs.apply q rentals)
              | RentalRepo.markNotified rentalId => do
                  markNotifiedSqlite conn rentalId
                  runShopIO conn (Arrs.apply q ())
              | RentalRepo.listCustomers => do
                  let customers ← listCustomersSqlite conn
                  runShopIO conn (Arrs.apply q customers)
              | RentalRepo.listMovies => do
                  let movies ← listMoviesSqlite conn
                  runShopIO conn (Arrs.apply q movies)
          | OpenUnion.there consoleUnion =>
              match consoleUnion with
              | OpenUnion.here request =>
                  match request with
                  | Console.printLine line => do
                      IO.println line
                      runShopIO conn (Arrs.apply q ())
                  | Console.readLine => do
                      let stdin ← IO.getStdin
                      let line ← stdin.getLine
                      runShopIO conn (Arrs.apply q (line.trimAscii.toString))
              | OpenUnion.there rest => OpenUnion.absurd rest

def runDemo (day : Day) : IO (Except ShopError Unit × List String) := do
  let conn ← openInMemorySqlite
  sqliteExec conn (initSql day)
  appProgram
    |> runReader ({ shopName := "Palladin's Video Rental" } : Config)
    |> runExcept (ε := ShopError)
    |> runWriter
    |> runShopIO conn

def errorMessage : ShopError → String
  | .unknownCustomer id => s!"unknown customer #{id}"
  | .unknownMovie id => s!"unknown movie #{id}"
  | .invalidPeriod days => s!"invalid rental period: {days} day(s)"

def printIoBox (title : String) (lines : List String) : IO Unit := do
  for line in box title lines do
    IO.println line

def printIoTable (title : String) (widths : List Nat) (header : List String)
    (rows : List (List String)) : IO Unit := do
  IO.println ""
  IO.println title
  IO.println (tableLine widths)
  IO.println (tableRow widths header)
  IO.println (tableLine widths)
  for row in rows do
    IO.println (tableRow widths row)
  IO.println (tableLine widths)

def main : IO Unit := do
  let day ← currentUnixDay
  printIoBox "Runtime" [s!"current rental day: {day}", "storage: in-memory SQLite"]
  let (result, outbox) ← runDemo day
  match result with
  | Except.ok _ =>
      printIoBox "Session" ["Session ended."]
  | Except.error error =>
      printIoBox "Session" [s!"failed: {errorMessage error}"]
  let rows := outbox.zipIdx.map fun (message, idx) =>
    [toString (idx + 1), message]
  printIoTable "Outbox" [4, 68] ["#", "Message"] rows

end Examples.VideoRental

def main : IO Unit :=
  Examples.VideoRental.main
