/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.spark.sql.hive

import java.util.{Set=>JSet}

import org.apache.hadoop.hive.ql.udf.generic.GenericUDFUtils.ConversionHelper
import org.apache.spark.sql.catalyst.expressions.aggregate2.{AggregateExpression2, COMPLETE, FINAL, PARTIAL1}
import org.apache.spark.sql.catalyst.planning.AggregateExpressionSubsitution

import scala.collection.mutable.ArrayBuffer

import org.apache.hadoop.hive.serde2.objectinspector.{ObjectInspector, ConstantObjectInspector}
import org.apache.hadoop.hive.serde2.objectinspector.ObjectInspectorFactory.ObjectInspectorOptions
import org.apache.hadoop.hive.serde2.objectinspector.ObjectInspectorFactory
import org.apache.hadoop.hive.ql.exec.{UDF, UDAF}
import org.apache.hadoop.hive.ql.exec.{FunctionInfo, FunctionRegistry}
import org.apache.hadoop.hive.ql.udf.{UDFType => HiveUDFType}
import org.apache.hadoop.hive.ql.udf.generic._
import org.apache.hadoop.hive.ql.udf.generic.GenericUDF._

import org.apache.spark.Logging
import org.apache.spark.sql.catalyst.analysis
import org.apache.spark.sql.catalyst.expressions._
import org.apache.spark.sql.catalyst.plans.logical.{Generate, Project, LogicalPlan}
import org.apache.spark.sql.catalyst.rules.Rule
import org.apache.spark.sql.types._
import org.apache.spark.sql.catalyst.analysis.MultiAlias
import org.apache.spark.sql.catalyst.errors.TreeNodeException

/* Implicit conversions */
import scala.collection.JavaConversions._

private[hive] abstract class HiveFunctionRegistry
  extends analysis.FunctionRegistry with HiveInspectors {

  def getFunctionInfo(name: String): FunctionInfo = FunctionRegistry.getFunctionInfo(name)

  def lookupFunction(name: String, children: Seq[Expression]): Expression = {
    // We only look it up to see if it exists, but do not include it in the HiveUDF since it is
    // not always serializable.
    val functionInfo: FunctionInfo =
      Option(FunctionRegistry.getFunctionInfo(name.toLowerCase)).getOrElse(
        sys.error(s"Couldn't find function $name"))

    val functionClassName = functionInfo.getFunctionClass.getName

    if (classOf[UDF].isAssignableFrom(functionInfo.getFunctionClass)) {
      HiveSimpleUdf(new HiveFunctionWrapper(functionClassName), children)
    } else if (classOf[GenericUDF].isAssignableFrom(functionInfo.getFunctionClass)) {
      HiveGenericUdf(new HiveFunctionWrapper(functionClassName), children)
    } else if (
         classOf[AbstractGenericUDAFResolver].isAssignableFrom(functionInfo.getFunctionClass)) {
      HiveGenericUdaf(new HiveFunctionWrapper(functionClassName), children)
    } else if (classOf[UDAF].isAssignableFrom(functionInfo.getFunctionClass)) {
      HiveUdaf(new HiveFunctionWrapper(functionClassName), children)
    } else if (classOf[GenericUDTF].isAssignableFrom(functionInfo.getFunctionClass)) {
      HiveGenericUdtf(new HiveFunctionWrapper(functionClassName), children)
    } else {
      sys.error(s"No handler for udf ${functionInfo.getFunctionClass}")
    }
  }
}

private[hive] case class HiveSimpleUdf(funcWrapper: HiveFunctionWrapper, children: Seq[Expression])
  extends Expression with HiveInspectors with Logging {
  type EvaluatedType = Any
  type UDFType = UDF

  override def nullable: Boolean = true

  @transient
  lazy val function = funcWrapper.createFunction[UDFType]()

  @transient
  protected lazy val method =
    function.getResolver.getEvalMethod(children.map(_.dataType.toTypeInfo))

  @transient
  protected lazy val arguments = children.map(toInspector).toArray

  @transient
  protected lazy val isUDFDeterministic = {
    val udfType = function.getClass().getAnnotation(classOf[HiveUDFType])
    udfType != null && udfType.deterministic()
  }

  override def foldable: Boolean = isUDFDeterministic && children.forall(_.foldable)

  // Create parameter converters
  @transient
  protected lazy val conversionHelper = new ConversionHelper(method, arguments)

  @transient
  lazy val dataType = javaClassToDataType(method.getReturnType)

  @transient
  lazy val returnInspector = ObjectInspectorFactory.getReflectionObjectInspector(
    method.getGenericReturnType(), ObjectInspectorOptions.JAVA)

  @transient
  protected lazy val cached: Array[AnyRef] = new Array[AnyRef](children.length)

  // TODO: Finish input output types.
  override def eval(input: Row): Any = {
    unwrap(
      FunctionRegistry.invoke(method, function, conversionHelper
        .convertIfNecessary(wrap(children.map(c => c.eval(input)), arguments, cached): _*): _*),
      returnInspector)
  }

  override def toString: String = {
    s"$nodeName#${funcWrapper.functionClassName}(${children.mkString(",")})"
  }
}

// Adapter from Catalyst ExpressionResult to Hive DeferredObject
private[hive] class DeferredObjectAdapter(oi: ObjectInspector)
  extends DeferredObject with HiveInspectors {
  private var func: () => Any = _
  def set(func: () => Any): Unit = {
    this.func = func
  }
  override def prepare(i: Int): Unit = {}
  override def get(): AnyRef = wrap(func(), oi)
}

private[hive] case class HiveGenericUdf(funcWrapper: HiveFunctionWrapper, children: Seq[Expression])
  extends Expression with HiveInspectors with Logging {
  type UDFType = GenericUDF
  type EvaluatedType = Any

  override def nullable: Boolean = true

  @transient
  lazy val function = funcWrapper.createFunction[UDFType]()

  @transient
  protected lazy val argumentInspectors = children.map(toInspector)

  @transient
  protected lazy val returnInspector = {
    function.initializeAndFoldConstants(argumentInspectors.toArray)
  }

  @transient
  protected lazy val isUDFDeterministic = {
    val udfType = function.getClass().getAnnotation(classOf[HiveUDFType])
    (udfType != null && udfType.deterministic())
  }

  override def foldable: Boolean =
    isUDFDeterministic && returnInspector.isInstanceOf[ConstantObjectInspector]

  @transient
  protected lazy val deferedObjects =
    argumentInspectors.map(new DeferredObjectAdapter(_)).toArray[DeferredObject]

  lazy val dataType: DataType = inspectorToDataType(returnInspector)

  override def eval(input: Row): Any = {
    returnInspector // Make sure initialized.

    var i = 0
    while (i < children.length) {
      val idx = i
      deferedObjects(i).asInstanceOf[DeferredObjectAdapter].set(
        () => {
          children(idx).eval(input)
        })
      i += 1
    }
    unwrap(function.evaluate(deferedObjects), returnInspector)
  }

  override def toString: String = {
    s"$nodeName#${funcWrapper.functionClassName}(${children.mkString(",")})"
  }
}

private[hive] case class HiveGenericUdaf(
    funcWrapper: HiveFunctionWrapper,
    children: Seq[Expression]) extends AggregateExpression
  with HiveInspectors {

  type UDFType = AbstractGenericUDAFResolver

  @transient
  protected lazy val resolver: AbstractGenericUDAFResolver = funcWrapper.createFunction()

  @transient
  protected lazy val objectInspector  = {
    val parameterInfo = new SimpleGenericUDAFParameterInfo(inspectors.toArray, false, false)
    resolver.getEvaluator(parameterInfo)
      .init(GenericUDAFEvaluator.Mode.COMPLETE, inspectors.toArray)
  }

  @transient
  protected lazy val inspectors = children.map(toInspector)

  def dataType: DataType = inspectorToDataType(objectInspector)

  def nullable: Boolean = true

  override def toString: String = {
    s"$nodeName#${funcWrapper.functionClassName}(${children.mkString(",")})"
  }

  def newInstance(): HiveUdafFunction = new HiveUdafFunction(funcWrapper, children, this)
}

/** It is used as a wrapper for the hive functions which uses UDAF interface */
private[hive] case class HiveUdaf(
    funcWrapper: HiveFunctionWrapper,
    children: Seq[Expression]) extends AggregateExpression
  with HiveInspectors {

  type UDFType = UDAF

  @transient
  protected lazy val resolver: AbstractGenericUDAFResolver =
    new GenericUDAFBridge(funcWrapper.createFunction())

  @transient
  protected lazy val objectInspector  = {
    val parameterInfo = new SimpleGenericUDAFParameterInfo(inspectors.toArray, false, false)
    resolver.getEvaluator(parameterInfo)
      .init(GenericUDAFEvaluator.Mode.COMPLETE, inspectors.toArray)
  }

  @transient
  protected lazy val inspectors = children.map(toInspector)

  def dataType: DataType = inspectorToDataType(objectInspector)

  def nullable: Boolean = true

  override def toString: String = {
    s"$nodeName#${funcWrapper.functionClassName}(${children.mkString(",")})"
  }

  def newInstance(): HiveUdafFunction = new HiveUdafFunction(funcWrapper, children, this, true)
}

private[hive] case class HiveGenericUdaf2(
    funcWrapper: HiveFunctionWrapper,
    children: Seq[Expression],
    distinct: Boolean,
    isSimpleUDAF: Boolean) extends AggregateExpression2 with HiveInspectors {
  type UDFType = AbstractGenericUDAFResolver

  protected def createEvaluator = resolver.getEvaluator(
    new SimpleGenericUDAFParameterInfo(inspectors, false, false))

  // Hive UDAF evaluator
  @transient
  lazy val evaluator = createEvaluator

  @transient
  protected lazy val resolver: AbstractGenericUDAFResolver = if (isSimpleUDAF) {
    // if it's the Simple UDAF, we need the UDAF bridge
    new GenericUDAFBridge(funcWrapper.createFunction())
  } else {
    funcWrapper.createFunction()
  }

  // Output data object inspector
  @transient
  lazy val objectInspector = createEvaluator.init(GenericUDAFEvaluator.Mode.COMPLETE, inspectors)

  // Aggregation Buffer Inspector
  @transient
  lazy val bufferObjectInspector = {
    createEvaluator.init(GenericUDAFEvaluator.Mode.PARTIAL1, inspectors)
  }

  // Input arguments object inspectors
  @transient
  lazy val inspectors = children.map(toInspector).toArray

  private val distinctLike: Boolean = {
    val annotation = evaluator.getClass().getAnnotation(classOf[HiveUDFType])
    if (annotation == null || !annotation.distinctLike()) false else true
  }
  override def toString: String =
    s"$nodeName#${funcWrapper.functionClassName}(${children.mkString(",")})"

  // Aggregation Buffer Data Type, We assume only 1 element for the Hive Aggregation Buffer
  // It will be StructType if more than 1 element (Actually will be StructSettableObjectInspector)
  override def bufferDataType: Seq[DataType] = inspectorToDataType(bufferObjectInspector) :: Nil

  // Output data type
  override def dataType: DataType = inspectorToDataType(objectInspector)

  ///////////////////////////////////////////////////////////////////////////////////////////////
  //            The following code will be called within the executors                         //
  ///////////////////////////////////////////////////////////////////////////////////////////////
  @transient var bound: BoundReference = _

  override def initialize(buffers: Seq[BoundReference]): Unit = {
    bound = buffers(0)
    mode match {
      case FINAL => evaluator.init(GenericUDAFEvaluator.Mode.FINAL, Array(bufferObjectInspector))
      case COMPLETE => evaluator.init(GenericUDAFEvaluator.Mode.COMPLETE, inspectors)
      case PARTIAL1 => evaluator.init(GenericUDAFEvaluator.Mode.PARTIAL1, inspectors)
    }
  }

  // Initialize (reinitialize) the aggregation buffer
  override def reset(buf: MutableRow): Unit = {
    val buffer = evaluator.getNewAggregationBuffer
    evaluator.reset(buffer)
    // This is a hack, we never use the mutable row as buffer, but define our own buffer,
    // which is set as the first element of the buffer
    buf(bound) = buffer
  }

  // Expect the aggregate function fills the aggregation buffer when fed with each value
  // in the group
  override def update(input: Row, buf: MutableRow, seen: JSet[Any]): Unit = {
    val arguments = children.map(_.eval(input))
    // We assume the memory is much more critical than computation,
    // so we prefer computation other than put the into a in-memory Set
    // when the UDAF is distinct-Like
    if (distinctLike || !distinct || !seen.contains(arguments)) {
      val args = arguments.zip(inspectors).map {
        case (value, oi) => wrap(value, oi)
      }.toArray

      evaluator.iterate(
        buf.getAs[GenericUDAFEvaluator.AggregationBuffer](bound.ordinal), args)
      if (distinct && !distinctLike) seen.add(arguments)
    }
  }

  // Merge 2 aggregation buffer, and write back to the later one
  override def merge(value: Row, buf: MutableRow): Unit = {
    val buffer = buf.getAs[GenericUDAFEvaluator.AggregationBuffer](bound.ordinal)
    evaluator.merge(buffer, wrap(value.get(bound.ordinal), bufferObjectInspector))
  }

  @deprecated
  override def terminatePartial(buf: MutableRow): Unit = {
    val buffer = buf.getAs[GenericUDAFEvaluator.AggregationBuffer](bound.ordinal)
    // this is for serialization
    buf(bound) = unwrap(evaluator.terminatePartial(buffer), bufferObjectInspector)
  }

  // Output the final result by feeding the aggregation buffer
  override def terminate(input: Row): Any = {
    unwrap(evaluator.terminate(
      input.getAs[GenericUDAFEvaluator.AggregationBuffer](bound.ordinal)),
      objectInspector)
  }
}

/**
 * Converts a Hive Generic User Defined Table Generating Function (UDTF) to a
 * [[catalyst.expressions.Generator Generator]].  Note that the semantics of Generators do not allow
 * Generators to maintain state in between input rows.  Thus UDTFs that rely on partitioning
 * dependent operations like calls to `close()` before producing output will not operate the same as
 * in Hive.  However, in practice this should not affect compatibility for most sane UDTFs
 * (e.g. explode or GenericUDTFParseUrlTuple).
 *
 * Operators that require maintaining state in between input rows should instead be implemented as
 * user defined aggregations, which have clean semantics even in a partitioned execution.
 */
private[hive] case class HiveGenericUdtf(
    funcWrapper: HiveFunctionWrapper,
    children: Seq[Expression])
  extends Generator with HiveInspectors {

  @transient
  protected lazy val function: GenericUDTF = funcWrapper.createFunction()

  @transient
  protected lazy val inputInspectors = children.map(toInspector)

  @transient
  protected lazy val outputInspector = function.initialize(inputInspectors.toArray)

  @transient
  protected lazy val udtInput = new Array[AnyRef](children.length)

  lazy val elementTypes = outputInspector.getAllStructFieldRefs.map {
    field => (inspectorToDataType(field.getFieldObjectInspector), true)
  }

  override def eval(input: Row): TraversableOnce[Row] = {
    outputInspector // Make sure initialized.

    val inputProjection = new InterpretedProjection(children)
    val collector = new UDTFCollector
    function.setCollector(collector)
    function.process(wrap(inputProjection(input), inputInspectors, udtInput))
    collector.collectRows()
  }

  protected class UDTFCollector extends Collector {
    var collected = new ArrayBuffer[Row]

    override def collect(input: java.lang.Object) {
      // We need to clone the input here because implementations of
      // GenericUDTF reuse the same object. Luckily they are always an array, so
      // it is easy to clone.
      collected += unwrap(input, outputInspector).asInstanceOf[Row]
    }

    def collectRows(): Seq[Row] = {
      val toCollect = collected
      collected = new ArrayBuffer[Row]
      toCollect
    }
  }

  override def toString: String = {
    s"$nodeName#${funcWrapper.functionClassName}(${children.mkString(",")})"
  }
}

private[hive] case class HiveUdafFunction(
    funcWrapper: HiveFunctionWrapper,
    exprs: Seq[Expression],
    base: AggregateExpression,
    isUDAFBridgeRequired: Boolean = false)
  extends AggregateFunction
  with HiveInspectors {

  def this() = this(null, null, null)

  private val resolver =
    if (isUDAFBridgeRequired) {
      new GenericUDAFBridge(funcWrapper.createFunction[UDAF]())
    } else {
      funcWrapper.createFunction[AbstractGenericUDAFResolver]()
    }
  
  private val inspectors = exprs.map(toInspector).toArray
    
  private val function = { 
    val parameterInfo = new SimpleGenericUDAFParameterInfo(inspectors, false, false)
    resolver.getEvaluator(parameterInfo) 
  }

  private val returnInspector = function.init(GenericUDAFEvaluator.Mode.COMPLETE, inspectors)

  private val buffer =
    function.getNewAggregationBuffer

  override def eval(input: Row): Any = unwrap(function.evaluate(buffer), returnInspector)

  @transient
  val inputProjection = new InterpretedProjection(exprs)

  @transient
  protected lazy val cached = new Array[AnyRef](exprs.length)
  
  def update(input: Row): Unit = {
    val inputs = inputProjection(input)
    function.iterate(buffer, wrap(inputs, inspectors, cached))
  }
}

private[hive] object HiveAggregateExpressionSubsitution extends AggregateExpressionSubsitution {
  override def subsitute(aggr: AggregateExpression): AggregateExpression2 = aggr match {
    // TODO: we don't support distinct for Hive UDAF(Generic) yet from the HiveQL Parser yet
    case HiveGenericUdaf(funcWrapper, children) =>
      HiveGenericUdaf2(funcWrapper, children, distinct = false, isSimpleUDAF = false)
    case HiveUdaf(funcWrapper, children) =>
      HiveGenericUdaf2(funcWrapper, children, distinct = false, isSimpleUDAF = true)
    case _ => super.subsitute(aggr)
  }
}
