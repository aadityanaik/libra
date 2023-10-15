package libra

import libra.nonrecursiveQueries.Rule

import java.io.File
import libra.util.Logging
import java.io.BufferedWriter
import java.io.FileWriter

case class Problem(
                    name: String,
                    inputRelations: Map[RelationName, Relation],
                    outputRelations: Map[RelationName, Relation],
                    types: Map[String, Type],
                    hypothesisSpace: scala.collection.SortedSet[Rule]
                  ) {

  require((inputRelations.keySet & outputRelations.keySet).isEmpty)
  for ((relName, relation) <- inputRelations ++ outputRelations) {
    require(relName.schema == relation.schema,
      s"Mismatched schema between relation name $relName and relation $relation")
  }

  val domains: Map[Domain, Set[Constant]] = {
    val allDomains = inputRelations.keySet.flatMap(_.schema) |
                     outputRelations.keySet.flatMap(_.schema)
    val ans = for (domain <- allDomains)
              yield domain -> {
                val ansDomain = for ((_, relation) <- inputRelations ++ outputRelations;
                                     i <- relation.schema.indices if relation.schema(i) == domain;
                                     t <- relation.tuples)
                                yield t(i)
                ansDomain.toSet: Set[Constant]
              }
    ans.toMap
  }

  def printHeader(printer: Any => Unit): Unit = {
    for (domainName <- domains.keys.toVector.map(_.toString).sorted) {
      printer(s".type $domainName")
    }
    printer("")

    def relNameStr(relName: RelationName): String = {
      var fieldStrs = Vector[String]()
      for (domain <- relName.schema) {
        var counter = 1
        var name = "" + domain.name(0).toLower + counter
        while (fieldStrs.contains(s"$name: $domain") ||
               domains.keys.exists(_.name == name)) {
          counter = counter + 1
          name = "" + domain.name(0).toLower + counter
        }
        fieldStrs = fieldStrs :+ s"$name: $domain"
      }
      s"${relName.name}(${fieldStrs.mkString(", ")})"
    }

    for (relName <- inputRelations.keys.toVector.sortBy(_.name)) {
      printer(s".decl ${relNameStr(relName)}")
      printer(s".input ${relName.name}")
    }
    printer("")

    for (relName <- outputRelations.keys.toVector.sortBy(_.name)) {
      printer(s".decl ${relNameStr(relName)}")
      printer(s".output ${relName.name}")
    }
    printer("")
  }

  def outputCSV(): Unit = {
    val nl = scala.util.Properties.lineSeparator
    for ((relName, relation) <- inputRelations) {
      val builder = new collection.mutable.StringBuilder()

      builder.append(s"${relName.schema.mkString(",")}" + nl)
      for (t <- relation.tuples.map(_.fields.map(_.name.replaceAll(",", "")).mkString(",")).toVector.sorted) {
        builder.append(t + nl)
      }

      val file = new File(name + "/" + relName.name + ".csv")
      val bw = new BufferedWriter(new FileWriter(file))
      bw.write(builder.toString)
      bw.close()
    }
    for ((relName, relation) <- outputRelations) {
      val builder = new collection.mutable.StringBuilder()

      builder.append(s"${relName.schema.mkString(",")}" + nl)
      for (t <- relation.tuples.map(_.fields.map(_.name.replaceAll(",", "")).mkString(",")).toVector.sorted) {
        builder.append(t + nl)
      }

      val file = new File(name + "/" + relName.name + ".csv")
      val bw = new BufferedWriter(new FileWriter(file))
      bw.write(builder.toString)
      bw.close()
    }
  }

  override def toString: String = {
    val nl = scala.util.Properties.lineSeparator
    val builder = new collection.mutable.StringBuilder()
    builder.append("Problem {" + nl)

    builder.append(s"  Domains:" + nl)
    for ((domain, constants) <- domains) {
      builder.append(s"    $domain:" + nl)
      for (c <- constants.toVector.map(_.toString).sorted) {
        builder.append(s"      $c" + nl)
      }
    }

    builder.append(s" Types:" + nl)
    for((name, _type) <- types) {
      builder.append(s" $name: ${_type.toString}" + nl)
    }

    builder.append("  Input Relations:" + nl)
    for ((relName, relation) <- inputRelations) {
      builder.append(s"    $relName" + nl)
      for (t <- relation.tuples.map(_.toString).toVector.sorted) {
        builder.append(s"      ${relName.name}($t)" + nl)
      }
    }

    builder.append("  Output Relations:" + nl)
    for ((relName, relation) <- outputRelations) {
      builder.append(s"    $relName" + nl)
      for (t <- relation.tuples.map(_.toString).toVector.sorted) {
        builder.append(s"      ${relName.name}($t)" + nl)
      }
    }

    builder.append("}")
    builder.toString
  }

}

object Problem {

  if (Options.RELAXED_PARSE) {
    Logging.info("Enabling relaxed parsing of relation files!")
  }

  def parseDecl(line: String): RelationName = {
    // .decl RelName(fieldName1: FieldType1, fieldName2: FieldType2, ..., fieldNamek: FieldTypek)
    val declLine = """\.decl\s+(\w+)\((.+)\)\s*""".r
    val fieldRegex = """.*:(.*)""".r
    line match {
      case declLine(relName, fieldsStr) =>
        val fieldTypes = fieldsStr.split(",").map {
          case fieldRegex(fieldType) => Domain(fieldType.strip())
        }
        RelationName(relName, fieldTypes.toVector)
    }
  }

  def loadRelation(relName: RelationName, file: File): Relation = {
    val source = scala.io.Source.fromFile(file)
    try {
      val tuples1 = for (line <- source.getLines())
                    yield (line, line.split("\t", relName.schema.length).map(_.strip()))
      val tuples2 = if (Options.RELAXED_PARSE) tuples1.filter(_._2.length == relName.schema.length) else tuples1
      val tuples3 = for ((line, components) <- tuples2)
                    yield {
                      require(components.length == relName.schema.length, s"Error while loading relation $relName: $line")
                      val fields = for ((c, cType) <- components.zip(relName.schema))
                                   yield Constant(if (c != "") c else "None", cType)
                      DTuple(fields.toVector)
                    }
      val tuples = tuples3
      Relation(relName.schema, tuples.toSet)
    } finally {
      source.close()
    }
  }

  def loadRelation(
                    problemFiles: Array[File],
                    declarations: Map[String, RelationName],
                    line: String
                  ): Option[(RelationName, Relation)] = {
    val inputRegex = """\.input\s+(\w+)""".r
    val outputRegex = """\.output\s+(\w+)""".r
    val (relName, filename) = line match {
      case inputRegex(relName) => (declarations(relName), s"$relName.facts")
      case outputRegex(relName) => (declarations(relName), s"$relName.expected")
    }
    val optFile = problemFiles.find(_.getName == filename)

    if (relName.name != "Rule" && optFile.nonEmpty) {
      Some((relName, loadRelation(relName, optFile.get)))
    } else if (relName.name == "Rule") {
      Logging.warn(s"Skipping relation Rule!")
      None
    } else {
      Logging.warn(s"Cannot find file $filename. Skipping!")
      None
    }
  }

  def loadType(line: String): Option[(String, Type)] = {
    val lineSplits = line.split(" ")
    // A type with spaces is allowed
    if(lineSplits.length >= 2) {
      val name = if (lineSplits.length > 2) {
        s"[${lineSplits.slice(1, lineSplits.length).mkString("").trim()}]"
      } else {
        lineSplits.slice(1, lineSplits.length).mkString("").trim()
      }
      Some((name, Type(name, NoComp)))
    } else {
      Logging.warn(s"Badly defined type on line `${line}`. Skipping!")
      None
    }
  }

  def apply(problemRules: String): Problem = {
    val rulesSmallDl = new File(problemRules)
    val dir = rulesSmallDl.getParentFile()
    val problemDirectory = dir.toString()
    require(dir.isDirectory())
    val problemFiles = dir.listFiles()

    var declarations = Map[String, RelationName]()
    var inputRelations = Map[RelationName, Relation]()
    var outputRelations = Map[RelationName, Relation]()
    val rulesSource = scala.io.Source.fromFile(rulesSmallDl)
    var types = Map[String, Type]()
    var hypothesisFile = new String()
    var hypothesisSpace = scala.collection.mutable.SortedSet[Rule]()
    try {
      for (line <- rulesSource.getLines()) {
        val trimmedLine : String = line.trim()
        if (trimmedLine.startsWith(".decl")) {
          val newDecl = parseDecl(trimmedLine)
          require(!declarations.contains(newDecl.name), s"Attempting to redeclare relation $newDecl.")
          declarations = declarations + (newDecl.name -> newDecl)
        } else if (trimmedLine.startsWith(".input")) {
          loadRelation(problemFiles, declarations, trimmedLine) match {
            case Some((relName, relation)) =>
              require(!inputRelations.contains(relName), s"Attempting to redefine relation $relName.")
              require(!outputRelations.contains(relName), s"Attempting to redefine relation $relName.")
              inputRelations = inputRelations + (relName -> relation)
            case None => ()
          }
        } else if (trimmedLine.startsWith(".output")) {
          loadRelation(problemFiles, declarations, trimmedLine) match {
            case Some((relName, relation)) =>
              require(!inputRelations.contains(relName), s"Attempting to redefine relation $relName.")
              require(!outputRelations.contains(relName), s"Attempting to redefine relation $relName.")
              outputRelations = outputRelations + (relName -> relation)
            case None => ()
          }
        } else if (trimmedLine.startsWith(".type")) {
          loadType(trimmedLine) match {
            case Some((name: String, _type: Type)) =>
              require(!types.contains(name))
              types += (name -> _type)
            case None => ()
          }
        } else if (trimmedLine.startsWith(".cat")) {
          val splits = trimmedLine.split(" ")
          val catTypeName = if (splits.length > 2) {
            s"[${splits.slice(1, splits.length).mkString("").trim()}]"
          } else {
            splits.slice(1, splits.length).mkString("").trim()
          }
          require(types.contains(catTypeName), s"Type $catTypeName not declared earlier.")
          val catType = types(catTypeName)
          catType.cmpType = Categorical
          types += (catTypeName -> catType)
        } else if (trimmedLine.startsWith(".ord")) {
          val splits = trimmedLine.split(" ")
          val typeName = if (splits.length > 2) {
            s"[${splits.slice(1, splits.length).mkString("").trim()}]"
          } else {
            splits.slice(1, splits.length).mkString("").trim()
          }
          require(types.contains(typeName), s"Type $typeName not declared earlier.")
          val catType = types(typeName)
          catType.cmpType = Ordered
          types += (typeName -> catType)
        } else if (trimmedLine.startsWith(".hspace")) {
          hypothesisFile = trimmedLine.split(" ")(1).trim()
          val hSource = scala.io.Source.fromFile(problemDirectory + "/" + hypothesisFile)
          // loading hypothesis space
          for(line <- hSource.getLines()) {
            hypothesisSpace.add(Rule(line, declarations))
          }
          hSource.close()
        } /* else ignore */
      }
    } finally {
      rulesSource.close()
    }

    val unitRelName = RelationName("$Unit", Vector())
    val unitRelation = Relation(unitRelName.schema, Set(DTuple()))
    require(!inputRelations.contains(unitRelName))
    inputRelations += unitRelName -> unitRelation

    Problem(problemDirectory, inputRelations, outputRelations, types, hypothesisSpace)
  }

}
