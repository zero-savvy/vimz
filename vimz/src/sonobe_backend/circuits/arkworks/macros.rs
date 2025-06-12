#[macro_export]
macro_rules! circuit_from_step_function {
    ($transformation: ident, $function: ident) => {
    paste::paste! {
        #[derive(Clone, Debug)]
        pub struct [<$transformation Arkworks Circuit>]<F: PrimeField> {
            poseidon_config: ark_crypto_primitives::sponge::poseidon::PoseidonConfig<F>,
        }

        impl<F: PrimeField + ark_crypto_primitives::sponge::Absorb> sonobe::frontend::FCircuit<F> for [<$transformation Arkworks Circuit>]<F> {
            type Params = ark_crypto_primitives::sponge::poseidon::PoseidonConfig<F>;
            type ExternalInputs = sonobe_frontends::utils::VecF<F, { Transformation::$transformation.step_input_width() }>;
            type ExternalInputsVar = sonobe_frontends::utils::VecFpVar<F, { Transformation::$transformation.step_input_width() }>;

            fn new(poseidon_config: Self::Params) -> Result<Self, sonobe::Error> {
                Ok(Self { poseidon_config })
            }

            fn state_len(&self) -> usize {
                Transformation::$transformation.ivc_state_len()
            }

            fn generate_step_constraints(
                &self,
                cs: ConstraintSystemRef<F>,
                _i: usize,
                z_i: Vec<FpVar<F>>,
                external_inputs: Self::ExternalInputsVar,
            ) -> Result<Vec<FpVar<F>>, SynthesisError> {
                assert_eq!(
                    z_i.len(),
                    Transformation::$transformation.ivc_state_len(),
                    "Invalid IVC state length for {}: expected {}, got {}",
                    stringify!($transformation),
                    Transformation::$transformation.ivc_state_len(),
                    z_i.len()
                );

                assert_eq!(
                    external_inputs.0.len(),
                    Transformation::$transformation.step_input_width(),
                    "Invalid input width for {}: expected {}, got {}",
                    stringify!($transformation),
                    Transformation::$transformation.step_input_width(),
                    external_inputs.0.len()
                );

                use ark_r1cs_std::alloc::AllocVar;
                let crh_params =
                    CRHParametersVar::<F>::new_constant(cs.clone(), self.poseidon_config.clone())?;

                $function(cs, z_i, external_inputs.0, crh_params)
            }
        }

        impl $crate::sonobe_backend::SonobeCircuit for [<$transformation Arkworks Circuit>] <ark_bn254::Fr> {
            fn from_config(_config: &$crate::config::Config) -> Self {
                <Self as sonobe::frontend::FCircuit<ark_bn254::Fr>>::new(
                    sonobe::transcript::poseidon::poseidon_canonical_config::<ark_bn254::Fr>()
                ).expect("Failed to construct HashStep from config")
            }
        }

    }
    };
}
