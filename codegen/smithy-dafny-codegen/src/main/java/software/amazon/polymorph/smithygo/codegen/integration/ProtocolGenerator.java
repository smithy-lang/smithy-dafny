/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *   http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */
package software.amazon.polymorph.smithygo.codegen.integration;

import static java.lang.String.format;

import software.amazon.polymorph.smithygo.codegen.ApplicationProtocol;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.utils.SmithyUnstableApi;

/**
 * Generates code to implement a protocol for both servers and clients.
 */
@SmithyUnstableApi
public interface ProtocolGenerator {
  /**
   * Gets the supported protocol {@link ShapeId}.
   *
   * @return Returns the protocol supported
   */
  ShapeId getProtocol();

  /**
   * Gets the name of the protocol.
   *
   * <p>The default implementation is the ShapeId name of the protocol trait in
   * Smithy models (e.g., "aws.protocols#restJson1" would return "restJson1").
   *
   * @return Returns the protocol name.
   */
  default String getName() {
    return getProtocol().getName();
  }

  /**
   * Creates an application protocol for the generator.
   *
   * @return Returns the created application protocol.
   */
  ApplicationProtocol getApplicationProtocol();

  /**
   * Generates the code used to serialize the shapes of a service
   * for requests.
   *
   * @param context Serialization context.
   */
  void generateSerializers(GenerationContext context);

  /**
   * Generates the code used to deserialize the shapes of a service
   * for responses.
   *
   * @param context Deserialization context.
   */
  void generateDeserializers(GenerationContext context);
}
