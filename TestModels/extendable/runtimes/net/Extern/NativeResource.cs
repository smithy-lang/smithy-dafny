using Simple.Extendable.Resources;

namespace DefaultNamespace
{
    public class NativeResource : ExtendableResourceBase
    {
        private readonly ExtendableResourceBase _impl;

        public NativeResource(ExtendableResourceBase nativeImpl)
        {
            this._impl = nativeImpl;
        }
        protected override GetResourceDataOutput _GetResourceData(GetResourceDataInput input)
        {
            return this._impl.GetResourceData(input);
        }

        protected override GetExtendableResourceErrorsOutput _AlwaysModeledError(GetExtendableResourceErrorsInput input)
        {
            return this._impl.AlwaysModeledError(input);
        }

        protected override GetExtendableResourceErrorsOutput _AlwaysMultipleErrors(GetExtendableResourceErrorsInput input)
        {
            return this._impl.AlwaysMultipleErrors(input);
        }

        protected override GetExtendableResourceErrorsOutput _AlwaysOpaqueError(GetExtendableResourceErrorsInput input)
        {
            return this._impl.AlwaysOpaqueError(input);
        }
    }
}
