use iri_string::types::UriString;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub mod ability;
pub mod caveats;

pub use ability::{
    Ability, AbilityName, AbilityNameRef, AbilityNamespace, AbilityNamespaceRef, AbilityRef,
};
pub use caveats::Caveats;

pub type CapsInner<C> = BTreeMap<UriString, BTreeMap<Ability, Caveats<C>>>;

/// Representation of a set of delegated Capabilities.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Capabilities<C>(CapsInner<C>);

#[derive(thiserror::Error, Debug)]
pub enum ConvertError<A, B> {
    #[error("Failed Conversion: {0}")]
    A(#[source] A),
    #[error("Failed Conversion: {0}")]
    B(#[source] B),
}

pub type ConvertResult<T, A, B, TA, TB> =
    Result<T, ConvertError<<TA as TryInto<A>>::Error, <TB as TryInto<B>>::Error>>;

impl<C> Capabilities<C> {
    /// Create a new empty set of Capabilities.
    pub fn new() -> Self {
        Self(CapsInner::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Check if a particular action is allowed for the specified target, or is allowed globally.
    pub fn can<T, A>(
        &self,
        target: T,
        action: A,
    ) -> ConvertResult<Option<&Caveats<C>>, UriString, Ability, T, A>
    where
        T: TryInto<UriString>,
        A: TryInto<Ability>,
    {
        Ok(self.can_do(
            &target.try_into().map_err(ConvertError::A)?,
            &action.try_into().map_err(ConvertError::B)?,
        ))
    }

    /// Check if a particular action is allowed for the specified target, or is allowed globally, without type conversion.
    pub fn can_do(&self, target: &UriString, action: &Ability) -> Option<&Caveats<C>> {
        self.0.get(target).and_then(|m| m.get(action))
    }

    /// Merge this Capabilities set with another
    pub fn merge<C1, C2>(self, other: Capabilities<C1>) -> Capabilities<C2>
    where
        C2: From<C1> + From<C>,
    {
        let mut s: Capabilities<C2> = self.0.into();
        let o: Capabilities<C2> = other.0.into();

        for (uri, abs) in o.0.into_iter() {
            let res_entry = s.0.entry(uri).or_default();
            for (ab, nbs) in abs.into_iter() {
                res_entry.entry(ab).or_default().extend(nbs);
            }
        }
        s
    }

    /// Merge this Capabilities set with another, where the two sets have different Nota Bene types.
    pub fn merge_convert<C1, C2>(
        self,
        other: Capabilities<C1>,
    ) -> ConvertResult<Capabilities<C2>, C2, C2, C, C1>
    where
        C2: TryFrom<C> + TryFrom<C1>,
    {
        Ok(try_convert(self)
            .map_err(ConvertError::A)?
            .merge(try_convert(other).map_err(ConvertError::B)?))
    }

    /// Add an allowed action for the given target, with a set of note-benes
    pub fn with_action(
        &mut self,
        target: UriString,
        action: Ability,
        nb: impl IntoIterator<Item = BTreeMap<String, C>>,
    ) -> &mut Self {
        self.0
            .entry(target)
            .or_default()
            .entry(action)
            .or_default()
            .extend(nb);
        self
    }

    /// Add an allowed action for the given target, with a set of note-benes.
    ///
    /// This method automatically converts the provided args into the correct types for convenience.
    pub fn with_action_convert<T, A>(
        &mut self,
        target: T,
        action: A,
        nb: impl IntoIterator<Item = BTreeMap<String, C>>,
    ) -> Result<&mut Self, ConvertError<T::Error, A::Error>>
    where
        T: TryInto<UriString>,
        A: TryInto<Ability>,
    {
        Ok(self.with_action(
            target.try_into().map_err(ConvertError::A)?,
            action.try_into().map_err(ConvertError::B)?,
            nb,
        ))
    }

    /// Add a set of allowed action for the given target, with associated note-benes
    pub fn with_actions(
        &mut self,
        target: UriString,
        abilities: impl IntoIterator<Item = (Ability, impl IntoIterator<Item = BTreeMap<String, C>>)>,
    ) -> &mut Self {
        let entry = self.0.entry(target).or_default();
        for (ability, nbs) in abilities {
            let ab_entry = entry.entry(ability).or_default();
            ab_entry.extend(nbs);
        }
        self
    }

    /// Add a set of allowed action for the given target, with associated note-benes.
    ///
    /// This method automatically converts the provided args into the correct types for convenience.
    pub fn with_actions_convert<T, A, N>(
        &mut self,
        target: T,
        abilities: impl IntoIterator<Item = (A, N)>,
    ) -> Result<&mut Self, ConvertError<T::Error, A::Error>>
    where
        T: TryInto<UriString>,
        A: TryInto<Ability>,
        N: IntoIterator<Item = BTreeMap<String, C>>,
    {
        Ok(self.with_actions(
            target.try_into().map_err(ConvertError::A)?,
            abilities
                .into_iter()
                .map(|(a, n)| Ok((a.try_into()?, n)))
                .collect::<Result<Vec<(Ability, N)>, A::Error>>()
                .map_err(ConvertError::B)?,
        ))
    }

    /// Read the set of abilities granted in this capabilities set
    pub fn abilities(&self) -> &CapsInner<C> {
        &self.0
    }

    /// Read the set of abilities granted for a given target in this capabilities set
    pub fn abilities_for<T>(
        &self,
        target: T,
    ) -> Result<Option<&BTreeMap<Ability, Caveats<C>>>, T::Error>
    where
        T: TryInto<UriString>,
    {
        Ok(self.0.get(&target.try_into()?))
    }

    pub fn into_inner(self) -> CapsInner<C> {
        self.0
    }
}

impl<C1, C2> From<CapsInner<C1>> for Capabilities<C2>
where
    C2: From<C1>,
{
    fn from(attenuations: CapsInner<C1>) -> Self {
        Self(
            attenuations
                .into_iter()
                .map(|(uri, abilities)| {
                    (
                        uri,
                        abilities
                            .into_iter()
                            .map(|(ability, nbs)| (ability, nbs.into_inner().into()))
                            .collect(),
                    )
                })
                .collect(),
        )
    }
}

pub fn try_convert<C1, C2>(caps: Capabilities<C1>) -> Result<Capabilities<C2>, C2::Error>
where
    C2: TryFrom<C1>,
{
    Ok(Capabilities(
        caps.0
            .into_iter()
            .map(|(uri, abilities)| {
                Ok((
                    uri,
                    abilities
                        .into_iter()
                        .map(|(ability, nbs)| Ok((ability, caveats::try_convert(nbs)?)))
                        .collect::<Result<BTreeMap<Ability, Caveats<C2>>, C2::Error>>()?,
                ))
            })
            .collect::<Result<CapsInner<C2>, C2::Error>>()?,
    ))
}

impl<C> Default for Capabilities<C> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insertion() {
        let mut caps = Capabilities::<String>::new();
        assert_eq!(caps.can("https://example.com", "crud/read").unwrap(), None);
        caps.with_action_convert("https://example.com", "crud/read", [])
            .unwrap();
        assert_eq!(
            caps.can("https://example.com", "crud/read")
                .unwrap()
                .unwrap(),
            &Caveats::<String>::new()
        );
    }

    #[test]
    fn merging() {
        let mut caps1 = Capabilities::<String>::new();
        caps1
            .with_action_convert(
                "https://example.com",
                "crud/read",
                [[("foo".into(), "bar".into())].into_iter().collect()],
            )
            .unwrap();

        let mut caps2 = Capabilities::<String>::new();
        caps2
            .with_action_convert("https://example.com", "crud/update", [])
            .unwrap()
            .with_action_convert("https://another.com", "crud/read", [])
            .unwrap();

        let mut caps_merged = Capabilities::<String>::new();
        caps_merged
            .with_action_convert(
                "https://example.com",
                "crud/read",
                [[("foo".into(), "bar".into())].into_iter().collect()],
            )
            .unwrap()
            .with_action_convert("https://example.com", "crud/update", [])
            .unwrap()
            .with_action_convert("https://another.com", "crud/read", [])
            .unwrap();

        assert_eq!(caps1.merge(caps2), caps_merged);
    }

    #[test]
    fn serde() {
        let mut caps = Capabilities::<String>::new();
        assert_eq!(serde_json::to_string(&caps).unwrap(), r#"{}"#);

        let with_one = r#"{"https://example.com/":{"crud/read":[{}]}}"#;

        caps.with_action_convert("https://example.com/", "crud/read", [])
            .unwrap();
        assert_eq!(serde_json::to_string(&caps).unwrap(), with_one);
        assert_eq!(
            serde_json::from_str::<Capabilities<String>>(with_one).unwrap(),
            caps
        );

        caps.with_action_convert(
            "https://example.com/",
            "crud/read",
            [[("foo".into(), "bar".into())].into_iter().collect()],
        )
        .unwrap();

        let with_two = r#"{"https://example.com/":{"crud/read":[{"foo":"bar"}]}}"#;
        assert_eq!(serde_json::to_string(&caps).unwrap(), with_two);
        assert_eq!(
            serde_json::from_str::<Capabilities<String>>(with_two).unwrap(),
            caps
        );

        let with_three = r#"{"https://another.com":{"crud/update":[{"bar":"baz"}]},"https://example.com/":{"crud/read":[{"foo":"bar"}]}}"#;
        caps.with_action_convert(
            "https://another.com",
            "crud/update",
            [[("bar".into(), "baz".into())].into_iter().collect()],
        )
        .unwrap();
        assert_eq!(serde_json::to_string(&caps).unwrap(), with_three);
        assert_eq!(
            serde_json::from_str::<Capabilities<String>>(with_three).unwrap(),
            caps
        );
    }
}
